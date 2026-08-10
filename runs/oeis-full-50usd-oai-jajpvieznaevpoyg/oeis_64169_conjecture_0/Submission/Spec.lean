import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000000

open Rat Finset

/-- A064169, as in the submission file. -/
def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  Int.natAbs (hn.num - hn.den)


private abbrev W : ℕ := 16843
private abbrev N : ℕ := W ^ 2
private abbrev M : ℕ := W ^ 3
private def D : ℕ := Nat.factorial (W - 1)
private def S : ℤ := ∑ k ∈ Finset.Ico (1:ℕ) W, (D / k : ℕ)

private def A : Finset ℕ := (Finset.Icc 2 (N - 2))
private def Mset : Finset ℕ := A.filter (fun k => W ∣ k)

private def Uset : Finset ℕ := A.filter (fun k => ¬ W ∣ k)

private lemma Wpos : 0 < W := by norm_num [W]
private lemma Wprime : Nat.Prime W := by norm_num [W]
private lemma WdvdN : W ∣ N := by unfold N; exact dvd_pow_self W (by norm_num)

private lemma sum_Ico_split {G : Type} [AddCommMonoid G] (f : ℕ → G) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ x ∈ Finset.Ico a c, f x = (∑ x ∈ Finset.Ico a b, f x) + (∑ x ∈ Finset.Ico b c, f x) := by
  rw [← Finset.sum_union]
  · rw [Finset.Ico_union_Ico_eq_Ico hab hbc]
  · exact Finset.Ico_disjoint_Ico_consecutive a b c
private lemma invChunk0 : (∑ k ∈ (Finset.Ico (1:ℕ) (101:ℕ)), ((k : ZMod M)⁻¹)) = (2492743516078 : ZMod M) := by decide
private lemma invChunk1 : (∑ k ∈ (Finset.Ico (101:ℕ) (201:ℕ)), ((k : ZMod M)⁻¹)) = (1672288710572 : ZMod M) := by decide
private lemma invChunk2 : (∑ k ∈ (Finset.Ico (201:ℕ) (301:ℕ)), ((k : ZMod M)⁻¹)) = (172678634977 : ZMod M) := by decide
private lemma invChunk3 : (∑ k ∈ (Finset.Ico (301:ℕ) (401:ℕ)), ((k : ZMod M)⁻¹)) = (3174624492187 : ZMod M) := by decide
private lemma invChunk4 : (∑ k ∈ (Finset.Ico (401:ℕ) (501:ℕ)), ((k : ZMod M)⁻¹)) = (400331769876 : ZMod M) := by decide
private lemma invChunk5 : (∑ k ∈ (Finset.Ico (501:ℕ) (601:ℕ)), ((k : ZMod M)⁻¹)) = (1106575843307 : ZMod M) := by decide
private lemma invChunk6 : (∑ k ∈ (Finset.Ico (601:ℕ) (701:ℕ)), ((k : ZMod M)⁻¹)) = (1184119579109 : ZMod M) := by decide
private lemma invChunk7 : (∑ k ∈ (Finset.Ico (701:ℕ) (801:ℕ)), ((k : ZMod M)⁻¹)) = (1587832900787 : ZMod M) := by decide
private lemma invChunk8 : (∑ k ∈ (Finset.Ico (801:ℕ) (901:ℕ)), ((k : ZMod M)⁻¹)) = (1023049974057 : ZMod M) := by decide
private lemma invChunk9 : (∑ k ∈ (Finset.Ico (901:ℕ) (1001:ℕ)), ((k : ZMod M)⁻¹)) = (3132384961908 : ZMod M) := by decide
private lemma invChunk10 : (∑ k ∈ (Finset.Ico (1001:ℕ) (1101:ℕ)), ((k : ZMod M)⁻¹)) = (904665549249 : ZMod M) := by decide
private lemma invChunk11 : (∑ k ∈ (Finset.Ico (1101:ℕ) (1201:ℕ)), ((k : ZMod M)⁻¹)) = (1301943680003 : ZMod M) := by decide
private lemma invChunk12 : (∑ k ∈ (Finset.Ico (1201:ℕ) (1301:ℕ)), ((k : ZMod M)⁻¹)) = (2866487879278 : ZMod M) := by decide
private lemma invChunk13 : (∑ k ∈ (Finset.Ico (1301:ℕ) (1401:ℕ)), ((k : ZMod M)⁻¹)) = (3739363286575 : ZMod M) := by decide
private lemma invChunk14 : (∑ k ∈ (Finset.Ico (1401:ℕ) (1501:ℕ)), ((k : ZMod M)⁻¹)) = (4435816788513 : ZMod M) := by decide
private lemma invChunk15 : (∑ k ∈ (Finset.Ico (1501:ℕ) (1601:ℕ)), ((k : ZMod M)⁻¹)) = (4741305438073 : ZMod M) := by decide
private lemma invChunk16 : (∑ k ∈ (Finset.Ico (1601:ℕ) (1701:ℕ)), ((k : ZMod M)⁻¹)) = (378849003726 : ZMod M) := by decide
private lemma invChunk17 : (∑ k ∈ (Finset.Ico (1701:ℕ) (1801:ℕ)), ((k : ZMod M)⁻¹)) = (1115987643354 : ZMod M) := by decide
private lemma invChunk18 : (∑ k ∈ (Finset.Ico (1801:ℕ) (1901:ℕ)), ((k : ZMod M)⁻¹)) = (4207793004669 : ZMod M) := by decide
private lemma invChunk19 : (∑ k ∈ (Finset.Ico (1901:ℕ) (2001:ℕ)), ((k : ZMod M)⁻¹)) = (2760863720158 : ZMod M) := by decide
private lemma invChunk20 : (∑ k ∈ (Finset.Ico (2001:ℕ) (2101:ℕ)), ((k : ZMod M)⁻¹)) = (2355927162162 : ZMod M) := by decide
private lemma invChunk21 : (∑ k ∈ (Finset.Ico (2101:ℕ) (2201:ℕ)), ((k : ZMod M)⁻¹)) = (429170207141 : ZMod M) := by decide
private lemma invChunk22 : (∑ k ∈ (Finset.Ico (2201:ℕ) (2301:ℕ)), ((k : ZMod M)⁻¹)) = (4000950743021 : ZMod M) := by decide
private lemma invChunk23 : (∑ k ∈ (Finset.Ico (2301:ℕ) (2401:ℕ)), ((k : ZMod M)⁻¹)) = (1259042469919 : ZMod M) := by decide
private lemma invChunk24 : (∑ k ∈ (Finset.Ico (2401:ℕ) (2501:ℕ)), ((k : ZMod M)⁻¹)) = (4571069669204 : ZMod M) := by decide
private lemma invChunk25 : (∑ k ∈ (Finset.Ico (2501:ℕ) (2601:ℕ)), ((k : ZMod M)⁻¹)) = (2965403963621 : ZMod M) := by decide
private lemma invChunk26 : (∑ k ∈ (Finset.Ico (2601:ℕ) (2701:ℕ)), ((k : ZMod M)⁻¹)) = (4319621200574 : ZMod M) := by decide
private lemma invChunk27 : (∑ k ∈ (Finset.Ico (2701:ℕ) (2801:ℕ)), ((k : ZMod M)⁻¹)) = (374721221475 : ZMod M) := by decide
private lemma invChunk28 : (∑ k ∈ (Finset.Ico (2801:ℕ) (2901:ℕ)), ((k : ZMod M)⁻¹)) = (4531849162099 : ZMod M) := by decide
private lemma invChunk29 : (∑ k ∈ (Finset.Ico (2901:ℕ) (3001:ℕ)), ((k : ZMod M)⁻¹)) = (1414475645660 : ZMod M) := by decide
private lemma invChunk30 : (∑ k ∈ (Finset.Ico (3001:ℕ) (3101:ℕ)), ((k : ZMod M)⁻¹)) = (651096737332 : ZMod M) := by decide
private lemma invChunk31 : (∑ k ∈ (Finset.Ico (3101:ℕ) (3201:ℕ)), ((k : ZMod M)⁻¹)) = (4580599068900 : ZMod M) := by decide
private lemma invChunk32 : (∑ k ∈ (Finset.Ico (3201:ℕ) (3301:ℕ)), ((k : ZMod M)⁻¹)) = (961445878722 : ZMod M) := by decide
private lemma invChunk33 : (∑ k ∈ (Finset.Ico (3301:ℕ) (3401:ℕ)), ((k : ZMod M)⁻¹)) = (3488981364933 : ZMod M) := by decide
private lemma invChunk34 : (∑ k ∈ (Finset.Ico (3401:ℕ) (3501:ℕ)), ((k : ZMod M)⁻¹)) = (3700991875971 : ZMod M) := by decide
private lemma invChunk35 : (∑ k ∈ (Finset.Ico (3501:ℕ) (3601:ℕ)), ((k : ZMod M)⁻¹)) = (4146800484825 : ZMod M) := by decide
private lemma invChunk36 : (∑ k ∈ (Finset.Ico (3601:ℕ) (3701:ℕ)), ((k : ZMod M)⁻¹)) = (3384471094820 : ZMod M) := by decide
private lemma invChunk37 : (∑ k ∈ (Finset.Ico (3701:ℕ) (3801:ℕ)), ((k : ZMod M)⁻¹)) = (2346798595163 : ZMod M) := by decide
private lemma invChunk38 : (∑ k ∈ (Finset.Ico (3801:ℕ) (3901:ℕ)), ((k : ZMod M)⁻¹)) = (2187812916030 : ZMod M) := by decide
private lemma invChunk39 : (∑ k ∈ (Finset.Ico (3901:ℕ) (4001:ℕ)), ((k : ZMod M)⁻¹)) = (3936118917988 : ZMod M) := by decide
private lemma invChunk40 : (∑ k ∈ (Finset.Ico (4001:ℕ) (4101:ℕ)), ((k : ZMod M)⁻¹)) = (2671119804207 : ZMod M) := by decide
private lemma invChunk41 : (∑ k ∈ (Finset.Ico (4101:ℕ) (4201:ℕ)), ((k : ZMod M)⁻¹)) = (2282004572335 : ZMod M) := by decide
private lemma invChunk42 : (∑ k ∈ (Finset.Ico (4201:ℕ) (4301:ℕ)), ((k : ZMod M)⁻¹)) = (767876083679 : ZMod M) := by decide
private lemma invChunk43 : (∑ k ∈ (Finset.Ico (4301:ℕ) (4401:ℕ)), ((k : ZMod M)⁻¹)) = (4774325782805 : ZMod M) := by decide
private lemma invChunk44 : (∑ k ∈ (Finset.Ico (4401:ℕ) (4501:ℕ)), ((k : ZMod M)⁻¹)) = (2092955105483 : ZMod M) := by decide
private lemma invChunk45 : (∑ k ∈ (Finset.Ico (4501:ℕ) (4601:ℕ)), ((k : ZMod M)⁻¹)) = (3549976999062 : ZMod M) := by decide
private lemma invChunk46 : (∑ k ∈ (Finset.Ico (4601:ℕ) (4701:ℕ)), ((k : ZMod M)⁻¹)) = (2219683074742 : ZMod M) := by decide
private lemma invChunk47 : (∑ k ∈ (Finset.Ico (4701:ℕ) (4801:ℕ)), ((k : ZMod M)⁻¹)) = (4751572091402 : ZMod M) := by decide
private lemma invChunk48 : (∑ k ∈ (Finset.Ico (4801:ℕ) (4901:ℕ)), ((k : ZMod M)⁻¹)) = (3396693052594 : ZMod M) := by decide
private lemma invChunk49 : (∑ k ∈ (Finset.Ico (4901:ℕ) (5001:ℕ)), ((k : ZMod M)⁻¹)) = (2648640477738 : ZMod M) := by decide
private lemma invChunk50 : (∑ k ∈ (Finset.Ico (5001:ℕ) (5101:ℕ)), ((k : ZMod M)⁻¹)) = (3210983579758 : ZMod M) := by decide
private lemma invChunk51 : (∑ k ∈ (Finset.Ico (5101:ℕ) (5201:ℕ)), ((k : ZMod M)⁻¹)) = (1566521613649 : ZMod M) := by decide
private lemma invChunk52 : (∑ k ∈ (Finset.Ico (5201:ℕ) (5301:ℕ)), ((k : ZMod M)⁻¹)) = (2182943365757 : ZMod M) := by decide
private lemma invChunk53 : (∑ k ∈ (Finset.Ico (5301:ℕ) (5401:ℕ)), ((k : ZMod M)⁻¹)) = (4105689758263 : ZMod M) := by decide
private lemma invChunk54 : (∑ k ∈ (Finset.Ico (5401:ℕ) (5501:ℕ)), ((k : ZMod M)⁻¹)) = (1975025684630 : ZMod M) := by decide
private lemma invChunk55 : (∑ k ∈ (Finset.Ico (5501:ℕ) (5601:ℕ)), ((k : ZMod M)⁻¹)) = (3875422326346 : ZMod M) := by decide
private lemma invChunk56 : (∑ k ∈ (Finset.Ico (5601:ℕ) (5701:ℕ)), ((k : ZMod M)⁻¹)) = (3233819704976 : ZMod M) := by decide
private lemma invChunk57 : (∑ k ∈ (Finset.Ico (5701:ℕ) (5801:ℕ)), ((k : ZMod M)⁻¹)) = (4071110372271 : ZMod M) := by decide
private lemma invChunk58 : (∑ k ∈ (Finset.Ico (5801:ℕ) (5901:ℕ)), ((k : ZMod M)⁻¹)) = (1479578301728 : ZMod M) := by decide
private lemma invChunk59 : (∑ k ∈ (Finset.Ico (5901:ℕ) (6001:ℕ)), ((k : ZMod M)⁻¹)) = (1588340361533 : ZMod M) := by decide
private lemma invChunk60 : (∑ k ∈ (Finset.Ico (6001:ℕ) (6101:ℕ)), ((k : ZMod M)⁻¹)) = (2587547475763 : ZMod M) := by decide
private lemma invChunk61 : (∑ k ∈ (Finset.Ico (6101:ℕ) (6201:ℕ)), ((k : ZMod M)⁻¹)) = (2014553460925 : ZMod M) := by decide
private lemma invChunk62 : (∑ k ∈ (Finset.Ico (6201:ℕ) (6301:ℕ)), ((k : ZMod M)⁻¹)) = (596354864661 : ZMod M) := by decide
private lemma invChunk63 : (∑ k ∈ (Finset.Ico (6301:ℕ) (6401:ℕ)), ((k : ZMod M)⁻¹)) = (1555439143411 : ZMod M) := by decide
private lemma invChunk64 : (∑ k ∈ (Finset.Ico (6401:ℕ) (6501:ℕ)), ((k : ZMod M)⁻¹)) = (1063676624762 : ZMod M) := by decide
private lemma invChunk65 : (∑ k ∈ (Finset.Ico (6501:ℕ) (6601:ℕ)), ((k : ZMod M)⁻¹)) = (722289195422 : ZMod M) := by decide
private lemma invChunk66 : (∑ k ∈ (Finset.Ico (6601:ℕ) (6701:ℕ)), ((k : ZMod M)⁻¹)) = (3317432932852 : ZMod M) := by decide
private lemma invChunk67 : (∑ k ∈ (Finset.Ico (6701:ℕ) (6801:ℕ)), ((k : ZMod M)⁻¹)) = (3438345474565 : ZMod M) := by decide
private lemma invChunk68 : (∑ k ∈ (Finset.Ico (6801:ℕ) (6901:ℕ)), ((k : ZMod M)⁻¹)) = (491540790525 : ZMod M) := by decide
private lemma invChunk69 : (∑ k ∈ (Finset.Ico (6901:ℕ) (7001:ℕ)), ((k : ZMod M)⁻¹)) = (4601837647159 : ZMod M) := by decide
private lemma invChunk70 : (∑ k ∈ (Finset.Ico (7001:ℕ) (7101:ℕ)), ((k : ZMod M)⁻¹)) = (3602491007309 : ZMod M) := by decide
private lemma invChunk71 : (∑ k ∈ (Finset.Ico (7101:ℕ) (7201:ℕ)), ((k : ZMod M)⁻¹)) = (1771264369479 : ZMod M) := by decide
private lemma invChunk72 : (∑ k ∈ (Finset.Ico (7201:ℕ) (7301:ℕ)), ((k : ZMod M)⁻¹)) = (1641076265401 : ZMod M) := by decide
private lemma invChunk73 : (∑ k ∈ (Finset.Ico (7301:ℕ) (7401:ℕ)), ((k : ZMod M)⁻¹)) = (3104508488297 : ZMod M) := by decide
private lemma invChunk74 : (∑ k ∈ (Finset.Ico (7401:ℕ) (7501:ℕ)), ((k : ZMod M)⁻¹)) = (2914322808164 : ZMod M) := by decide
private lemma invChunk75 : (∑ k ∈ (Finset.Ico (7501:ℕ) (7601:ℕ)), ((k : ZMod M)⁻¹)) = (1196190927420 : ZMod M) := by decide
private lemma invChunk76 : (∑ k ∈ (Finset.Ico (7601:ℕ) (7701:ℕ)), ((k : ZMod M)⁻¹)) = (2595801871275 : ZMod M) := by decide
private lemma invChunk77 : (∑ k ∈ (Finset.Ico (7701:ℕ) (7801:ℕ)), ((k : ZMod M)⁻¹)) = (491506439962 : ZMod M) := by decide
private lemma invChunk78 : (∑ k ∈ (Finset.Ico (7801:ℕ) (7901:ℕ)), ((k : ZMod M)⁻¹)) = (1329900318793 : ZMod M) := by decide
private lemma invChunk79 : (∑ k ∈ (Finset.Ico (7901:ℕ) (8001:ℕ)), ((k : ZMod M)⁻¹)) = (2238637938098 : ZMod M) := by decide
private lemma invChunk80 : (∑ k ∈ (Finset.Ico (8001:ℕ) (8101:ℕ)), ((k : ZMod M)⁻¹)) = (476646240388 : ZMod M) := by decide
private lemma invChunk81 : (∑ k ∈ (Finset.Ico (8101:ℕ) (8201:ℕ)), ((k : ZMod M)⁻¹)) = (1224678279069 : ZMod M) := by decide
private lemma invChunk82 : (∑ k ∈ (Finset.Ico (8201:ℕ) (8301:ℕ)), ((k : ZMod M)⁻¹)) = (4508770588903 : ZMod M) := by decide
private lemma invChunk83 : (∑ k ∈ (Finset.Ico (8301:ℕ) (8401:ℕ)), ((k : ZMod M)⁻¹)) = (773800577209 : ZMod M) := by decide
private lemma invChunk84 : (∑ k ∈ (Finset.Ico (8401:ℕ) (8501:ℕ)), ((k : ZMod M)⁻¹)) = (945264302746 : ZMod M) := by decide
private lemma invChunk85 : (∑ k ∈ (Finset.Ico (8501:ℕ) (8601:ℕ)), ((k : ZMod M)⁻¹)) = (4356416878945 : ZMod M) := by decide
private lemma invChunk86 : (∑ k ∈ (Finset.Ico (8601:ℕ) (8701:ℕ)), ((k : ZMod M)⁻¹)) = (3106781354914 : ZMod M) := by decide
private lemma invChunk87 : (∑ k ∈ (Finset.Ico (8701:ℕ) (8801:ℕ)), ((k : ZMod M)⁻¹)) = (2852469874663 : ZMod M) := by decide
private lemma invChunk88 : (∑ k ∈ (Finset.Ico (8801:ℕ) (8901:ℕ)), ((k : ZMod M)⁻¹)) = (512505819834 : ZMod M) := by decide
private lemma invChunk89 : (∑ k ∈ (Finset.Ico (8901:ℕ) (9001:ℕ)), ((k : ZMod M)⁻¹)) = (1820008051320 : ZMod M) := by decide
private lemma invChunk90 : (∑ k ∈ (Finset.Ico (9001:ℕ) (9101:ℕ)), ((k : ZMod M)⁻¹)) = (3574118156400 : ZMod M) := by decide
private lemma invChunk91 : (∑ k ∈ (Finset.Ico (9101:ℕ) (9201:ℕ)), ((k : ZMod M)⁻¹)) = (3931827558547 : ZMod M) := by decide
private lemma invChunk92 : (∑ k ∈ (Finset.Ico (9201:ℕ) (9301:ℕ)), ((k : ZMod M)⁻¹)) = (2448189672637 : ZMod M) := by decide
private lemma invChunk93 : (∑ k ∈ (Finset.Ico (9301:ℕ) (9401:ℕ)), ((k : ZMod M)⁻¹)) = (4044756403599 : ZMod M) := by decide
private lemma invChunk94 : (∑ k ∈ (Finset.Ico (9401:ℕ) (9501:ℕ)), ((k : ZMod M)⁻¹)) = (2015281427295 : ZMod M) := by decide
private lemma invChunk95 : (∑ k ∈ (Finset.Ico (9501:ℕ) (9601:ℕ)), ((k : ZMod M)⁻¹)) = (1160014837536 : ZMod M) := by decide
private lemma invChunk96 : (∑ k ∈ (Finset.Ico (9601:ℕ) (9701:ℕ)), ((k : ZMod M)⁻¹)) = (4405772198857 : ZMod M) := by decide
private lemma invChunk97 : (∑ k ∈ (Finset.Ico (9701:ℕ) (9801:ℕ)), ((k : ZMod M)⁻¹)) = (2804276635745 : ZMod M) := by decide
private lemma invChunk98 : (∑ k ∈ (Finset.Ico (9801:ℕ) (9901:ℕ)), ((k : ZMod M)⁻¹)) = (4249217201940 : ZMod M) := by decide
private lemma invChunk99 : (∑ k ∈ (Finset.Ico (9901:ℕ) (10001:ℕ)), ((k : ZMod M)⁻¹)) = (1152477025752 : ZMod M) := by decide
private lemma invChunk100 : (∑ k ∈ (Finset.Ico (10001:ℕ) (10101:ℕ)), ((k : ZMod M)⁻¹)) = (2023157357095 : ZMod M) := by decide
private lemma invChunk101 : (∑ k ∈ (Finset.Ico (10101:ℕ) (10201:ℕ)), ((k : ZMod M)⁻¹)) = (4345270218892 : ZMod M) := by decide
private lemma invChunk102 : (∑ k ∈ (Finset.Ico (10201:ℕ) (10301:ℕ)), ((k : ZMod M)⁻¹)) = (3582521726903 : ZMod M) := by decide
private lemma invChunk103 : (∑ k ∈ (Finset.Ico (10301:ℕ) (10401:ℕ)), ((k : ZMod M)⁻¹)) = (1263302288419 : ZMod M) := by decide
private lemma invChunk104 : (∑ k ∈ (Finset.Ico (10401:ℕ) (10501:ℕ)), ((k : ZMod M)⁻¹)) = (791554241292 : ZMod M) := by decide
private lemma invChunk105 : (∑ k ∈ (Finset.Ico (10501:ℕ) (10601:ℕ)), ((k : ZMod M)⁻¹)) = (3273871712861 : ZMod M) := by decide
private lemma invChunk106 : (∑ k ∈ (Finset.Ico (10601:ℕ) (10701:ℕ)), ((k : ZMod M)⁻¹)) = (3679769331404 : ZMod M) := by decide
private lemma invChunk107 : (∑ k ∈ (Finset.Ico (10701:ℕ) (10801:ℕ)), ((k : ZMod M)⁻¹)) = (3948509433872 : ZMod M) := by decide
private lemma invChunk108 : (∑ k ∈ (Finset.Ico (10801:ℕ) (10901:ℕ)), ((k : ZMod M)⁻¹)) = (4336295399767 : ZMod M) := by decide
private lemma invChunk109 : (∑ k ∈ (Finset.Ico (10901:ℕ) (11001:ℕ)), ((k : ZMod M)⁻¹)) = (2152685205163 : ZMod M) := by decide
private lemma invChunk110 : (∑ k ∈ (Finset.Ico (11001:ℕ) (11101:ℕ)), ((k : ZMod M)⁻¹)) = (4113876649232 : ZMod M) := by decide
private lemma invChunk111 : (∑ k ∈ (Finset.Ico (11101:ℕ) (11201:ℕ)), ((k : ZMod M)⁻¹)) = (3226241067936 : ZMod M) := by decide
private lemma invChunk112 : (∑ k ∈ (Finset.Ico (11201:ℕ) (11301:ℕ)), ((k : ZMod M)⁻¹)) = (316317092524 : ZMod M) := by decide
private lemma invChunk113 : (∑ k ∈ (Finset.Ico (11301:ℕ) (11401:ℕ)), ((k : ZMod M)⁻¹)) = (2696916088306 : ZMod M) := by decide
private lemma invChunk114 : (∑ k ∈ (Finset.Ico (11401:ℕ) (11501:ℕ)), ((k : ZMod M)⁻¹)) = (4483679938794 : ZMod M) := by decide
private lemma invChunk115 : (∑ k ∈ (Finset.Ico (11501:ℕ) (11601:ℕ)), ((k : ZMod M)⁻¹)) = (1592026250194 : ZMod M) := by decide
private lemma invChunk116 : (∑ k ∈ (Finset.Ico (11601:ℕ) (11701:ℕ)), ((k : ZMod M)⁻¹)) = (4421611059964 : ZMod M) := by decide
private lemma invChunk117 : (∑ k ∈ (Finset.Ico (11701:ℕ) (11801:ℕ)), ((k : ZMod M)⁻¹)) = (1573195190471 : ZMod M) := by decide
private lemma invChunk118 : (∑ k ∈ (Finset.Ico (11801:ℕ) (11901:ℕ)), ((k : ZMod M)⁻¹)) = (3097268369114 : ZMod M) := by decide
private lemma invChunk119 : (∑ k ∈ (Finset.Ico (11901:ℕ) (12001:ℕ)), ((k : ZMod M)⁻¹)) = (858105112040 : ZMod M) := by decide
private lemma invChunk120 : (∑ k ∈ (Finset.Ico (12001:ℕ) (12101:ℕ)), ((k : ZMod M)⁻¹)) = (1967503323339 : ZMod M) := by decide
private lemma invChunk121 : (∑ k ∈ (Finset.Ico (12101:ℕ) (12201:ℕ)), ((k : ZMod M)⁻¹)) = (70105671145 : ZMod M) := by decide
private lemma invChunk122 : (∑ k ∈ (Finset.Ico (12201:ℕ) (12301:ℕ)), ((k : ZMod M)⁻¹)) = (1828921721572 : ZMod M) := by decide
private lemma invChunk123 : (∑ k ∈ (Finset.Ico (12301:ℕ) (12401:ℕ)), ((k : ZMod M)⁻¹)) = (3223779148874 : ZMod M) := by decide
private lemma invChunk124 : (∑ k ∈ (Finset.Ico (12401:ℕ) (12501:ℕ)), ((k : ZMod M)⁻¹)) = (2558090942231 : ZMod M) := by decide
private lemma invChunk125 : (∑ k ∈ (Finset.Ico (12501:ℕ) (12601:ℕ)), ((k : ZMod M)⁻¹)) = (629550973919 : ZMod M) := by decide
private lemma invChunk126 : (∑ k ∈ (Finset.Ico (12601:ℕ) (12701:ℕ)), ((k : ZMod M)⁻¹)) = (2081284562938 : ZMod M) := by decide
private lemma invChunk127 : (∑ k ∈ (Finset.Ico (12701:ℕ) (12801:ℕ)), ((k : ZMod M)⁻¹)) = (4204236692438 : ZMod M) := by decide
private lemma invChunk128 : (∑ k ∈ (Finset.Ico (12801:ℕ) (12901:ℕ)), ((k : ZMod M)⁻¹)) = (3226412951709 : ZMod M) := by decide
private lemma invChunk129 : (∑ k ∈ (Finset.Ico (12901:ℕ) (13001:ℕ)), ((k : ZMod M)⁻¹)) = (3082774132655 : ZMod M) := by decide
private lemma invChunk130 : (∑ k ∈ (Finset.Ico (13001:ℕ) (13101:ℕ)), ((k : ZMod M)⁻¹)) = (413733676391 : ZMod M) := by decide
private lemma invChunk131 : (∑ k ∈ (Finset.Ico (13101:ℕ) (13201:ℕ)), ((k : ZMod M)⁻¹)) = (793737105373 : ZMod M) := by decide
private lemma invChunk132 : (∑ k ∈ (Finset.Ico (13201:ℕ) (13301:ℕ)), ((k : ZMod M)⁻¹)) = (1924624702408 : ZMod M) := by decide
private lemma invChunk133 : (∑ k ∈ (Finset.Ico (13301:ℕ) (13401:ℕ)), ((k : ZMod M)⁻¹)) = (126042230639 : ZMod M) := by decide
private lemma invChunk134 : (∑ k ∈ (Finset.Ico (13401:ℕ) (13501:ℕ)), ((k : ZMod M)⁻¹)) = (756351150780 : ZMod M) := by decide
private lemma invChunk135 : (∑ k ∈ (Finset.Ico (13501:ℕ) (13601:ℕ)), ((k : ZMod M)⁻¹)) = (1592420382990 : ZMod M) := by decide
private lemma invChunk136 : (∑ k ∈ (Finset.Ico (13601:ℕ) (13701:ℕ)), ((k : ZMod M)⁻¹)) = (4767231761208 : ZMod M) := by decide
private lemma invChunk137 : (∑ k ∈ (Finset.Ico (13701:ℕ) (13801:ℕ)), ((k : ZMod M)⁻¹)) = (1450724547169 : ZMod M) := by decide
private lemma invChunk138 : (∑ k ∈ (Finset.Ico (13801:ℕ) (13901:ℕ)), ((k : ZMod M)⁻¹)) = (860984154616 : ZMod M) := by decide
private lemma invChunk139 : (∑ k ∈ (Finset.Ico (13901:ℕ) (14001:ℕ)), ((k : ZMod M)⁻¹)) = (4499286128485 : ZMod M) := by decide
private lemma invChunk140 : (∑ k ∈ (Finset.Ico (14001:ℕ) (14101:ℕ)), ((k : ZMod M)⁻¹)) = (750677646539 : ZMod M) := by decide
private lemma invChunk141 : (∑ k ∈ (Finset.Ico (14101:ℕ) (14201:ℕ)), ((k : ZMod M)⁻¹)) = (4324853179683 : ZMod M) := by decide
private lemma invChunk142 : (∑ k ∈ (Finset.Ico (14201:ℕ) (14301:ℕ)), ((k : ZMod M)⁻¹)) = (2234206449284 : ZMod M) := by decide
private lemma invChunk143 : (∑ k ∈ (Finset.Ico (14301:ℕ) (14401:ℕ)), ((k : ZMod M)⁻¹)) = (3752696744057 : ZMod M) := by decide
private lemma invChunk144 : (∑ k ∈ (Finset.Ico (14401:ℕ) (14501:ℕ)), ((k : ZMod M)⁻¹)) = (69228875468 : ZMod M) := by decide
private lemma invChunk145 : (∑ k ∈ (Finset.Ico (14501:ℕ) (14601:ℕ)), ((k : ZMod M)⁻¹)) = (4470303298663 : ZMod M) := by decide
private lemma invChunk146 : (∑ k ∈ (Finset.Ico (14601:ℕ) (14701:ℕ)), ((k : ZMod M)⁻¹)) = (1693812016470 : ZMod M) := by decide
private lemma invChunk147 : (∑ k ∈ (Finset.Ico (14701:ℕ) (14801:ℕ)), ((k : ZMod M)⁻¹)) = (769030965782 : ZMod M) := by decide
private lemma invChunk148 : (∑ k ∈ (Finset.Ico (14801:ℕ) (14901:ℕ)), ((k : ZMod M)⁻¹)) = (1166408414193 : ZMod M) := by decide
private lemma invChunk149 : (∑ k ∈ (Finset.Ico (14901:ℕ) (15001:ℕ)), ((k : ZMod M)⁻¹)) = (1228718574404 : ZMod M) := by decide
private lemma invChunk150 : (∑ k ∈ (Finset.Ico (15001:ℕ) (15101:ℕ)), ((k : ZMod M)⁻¹)) = (1938960411286 : ZMod M) := by decide
private lemma invChunk151 : (∑ k ∈ (Finset.Ico (15101:ℕ) (15201:ℕ)), ((k : ZMod M)⁻¹)) = (1398067593989 : ZMod M) := by decide
private lemma invChunk152 : (∑ k ∈ (Finset.Ico (15201:ℕ) (15301:ℕ)), ((k : ZMod M)⁻¹)) = (2012169470528 : ZMod M) := by decide
private lemma invChunk153 : (∑ k ∈ (Finset.Ico (15301:ℕ) (15401:ℕ)), ((k : ZMod M)⁻¹)) = (2462779516442 : ZMod M) := by decide
private lemma invChunk154 : (∑ k ∈ (Finset.Ico (15401:ℕ) (15501:ℕ)), ((k : ZMod M)⁻¹)) = (2939482891417 : ZMod M) := by decide
private lemma invChunk155 : (∑ k ∈ (Finset.Ico (15501:ℕ) (15601:ℕ)), ((k : ZMod M)⁻¹)) = (35286005863 : ZMod M) := by decide
private lemma invChunk156 : (∑ k ∈ (Finset.Ico (15601:ℕ) (15701:ℕ)), ((k : ZMod M)⁻¹)) = (975835070465 : ZMod M) := by decide
private lemma invChunk157 : (∑ k ∈ (Finset.Ico (15701:ℕ) (15801:ℕ)), ((k : ZMod M)⁻¹)) = (1693314774320 : ZMod M) := by decide
private lemma invChunk158 : (∑ k ∈ (Finset.Ico (15801:ℕ) (15901:ℕ)), ((k : ZMod M)⁻¹)) = (998213319685 : ZMod M) := by decide
private lemma invChunk159 : (∑ k ∈ (Finset.Ico (15901:ℕ) (16001:ℕ)), ((k : ZMod M)⁻¹)) = (2419289843257 : ZMod M) := by decide
private lemma invChunk160 : (∑ k ∈ (Finset.Ico (16001:ℕ) (16101:ℕ)), ((k : ZMod M)⁻¹)) = (3599822339383 : ZMod M) := by decide
private lemma invChunk161 : (∑ k ∈ (Finset.Ico (16101:ℕ) (16201:ℕ)), ((k : ZMod M)⁻¹)) = (4224092856692 : ZMod M) := by decide
private lemma invChunk162 : (∑ k ∈ (Finset.Ico (16201:ℕ) (16301:ℕ)), ((k : ZMod M)⁻¹)) = (2930980998319 : ZMod M) := by decide
private lemma invChunk163 : (∑ k ∈ (Finset.Ico (16301:ℕ) (16401:ℕ)), ((k : ZMod M)⁻¹)) = (3482176622388 : ZMod M) := by decide
private lemma invChunk164 : (∑ k ∈ (Finset.Ico (16401:ℕ) (16501:ℕ)), ((k : ZMod M)⁻¹)) = (3882202685396 : ZMod M) := by decide
private lemma invChunk165 : (∑ k ∈ (Finset.Ico (16501:ℕ) (16601:ℕ)), ((k : ZMod M)⁻¹)) = (280668986540 : ZMod M) := by decide
private lemma invChunk166 : (∑ k ∈ (Finset.Ico (16601:ℕ) (16701:ℕ)), ((k : ZMod M)⁻¹)) = (4035532809555 : ZMod M) := by decide
private lemma invChunk167 : (∑ k ∈ (Finset.Ico (16701:ℕ) (16801:ℕ)), ((k : ZMod M)⁻¹)) = (1929128158165 : ZMod M) := by decide
private lemma invChunk168 : (∑ k ∈ (Finset.Ico (16801:ℕ) (16843:ℕ)), ((k : ZMod M)⁻¹)) = (2520171261224 : ZMod M) := by decide
private lemma inv_sum_zmod_zero : (∑ k ∈ (Finset.Ico (1:ℕ) W), ((k : ZMod M)⁻¹)) = 0 := by
  norm_num [W]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1) (b := 101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 101) (b := 201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 201) (b := 301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 301) (b := 401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 401) (b := 501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 501) (b := 601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 601) (b := 701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 701) (b := 801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 801) (b := 901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 901) (b := 1001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1001) (b := 1101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1101) (b := 1201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1201) (b := 1301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1301) (b := 1401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1401) (b := 1501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1501) (b := 1601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1601) (b := 1701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1701) (b := 1801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1801) (b := 1901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 1901) (b := 2001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2001) (b := 2101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2101) (b := 2201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2201) (b := 2301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2301) (b := 2401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2401) (b := 2501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2501) (b := 2601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2601) (b := 2701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2701) (b := 2801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2801) (b := 2901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 2901) (b := 3001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3001) (b := 3101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3101) (b := 3201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3201) (b := 3301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3301) (b := 3401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3401) (b := 3501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3501) (b := 3601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3601) (b := 3701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3701) (b := 3801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3801) (b := 3901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 3901) (b := 4001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4001) (b := 4101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4101) (b := 4201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4201) (b := 4301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4301) (b := 4401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4401) (b := 4501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4501) (b := 4601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4601) (b := 4701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4701) (b := 4801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4801) (b := 4901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 4901) (b := 5001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5001) (b := 5101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5101) (b := 5201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5201) (b := 5301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5301) (b := 5401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5401) (b := 5501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5501) (b := 5601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5601) (b := 5701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5701) (b := 5801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5801) (b := 5901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 5901) (b := 6001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6001) (b := 6101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6101) (b := 6201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6201) (b := 6301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6301) (b := 6401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6401) (b := 6501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6501) (b := 6601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6601) (b := 6701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6701) (b := 6801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6801) (b := 6901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 6901) (b := 7001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7001) (b := 7101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7101) (b := 7201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7201) (b := 7301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7301) (b := 7401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7401) (b := 7501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7501) (b := 7601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7601) (b := 7701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7701) (b := 7801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7801) (b := 7901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 7901) (b := 8001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8001) (b := 8101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8101) (b := 8201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8201) (b := 8301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8301) (b := 8401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8401) (b := 8501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8501) (b := 8601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8601) (b := 8701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8701) (b := 8801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8801) (b := 8901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 8901) (b := 9001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9001) (b := 9101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9101) (b := 9201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9201) (b := 9301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9301) (b := 9401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9401) (b := 9501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9501) (b := 9601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9601) (b := 9701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9701) (b := 9801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9801) (b := 9901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 9901) (b := 10001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10001) (b := 10101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10101) (b := 10201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10201) (b := 10301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10301) (b := 10401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10401) (b := 10501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10501) (b := 10601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10601) (b := 10701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10701) (b := 10801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10801) (b := 10901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 10901) (b := 11001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11001) (b := 11101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11101) (b := 11201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11201) (b := 11301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11301) (b := 11401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11401) (b := 11501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11501) (b := 11601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11601) (b := 11701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11701) (b := 11801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11801) (b := 11901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 11901) (b := 12001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12001) (b := 12101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12101) (b := 12201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12201) (b := 12301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12301) (b := 12401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12401) (b := 12501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12501) (b := 12601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12601) (b := 12701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12701) (b := 12801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12801) (b := 12901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 12901) (b := 13001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13001) (b := 13101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13101) (b := 13201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13201) (b := 13301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13301) (b := 13401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13401) (b := 13501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13501) (b := 13601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13601) (b := 13701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13701) (b := 13801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13801) (b := 13901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 13901) (b := 14001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14001) (b := 14101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14101) (b := 14201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14201) (b := 14301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14301) (b := 14401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14401) (b := 14501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14501) (b := 14601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14601) (b := 14701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14701) (b := 14801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14801) (b := 14901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 14901) (b := 15001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15001) (b := 15101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15101) (b := 15201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15201) (b := 15301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15301) (b := 15401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15401) (b := 15501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15501) (b := 15601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15601) (b := 15701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15701) (b := 15801) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15801) (b := 15901) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 15901) (b := 16001) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16001) (b := 16101) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16101) (b := 16201) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16201) (b := 16301) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16301) (b := 16401) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16401) (b := 16501) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16501) (b := 16601) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16601) (b := 16701) (c := 16843) (by norm_num) (by norm_num)]
  rw [sum_Ico_split (fun k : ℕ => ((k : ZMod M)⁻¹)) (a := 16701) (b := 16801) (c := 16843) (by norm_num) (by norm_num)]
  rw [invChunk0]
  rw [invChunk1]
  rw [invChunk2]
  rw [invChunk3]
  rw [invChunk4]
  rw [invChunk5]
  rw [invChunk6]
  rw [invChunk7]
  rw [invChunk8]
  rw [invChunk9]
  rw [invChunk10]
  rw [invChunk11]
  rw [invChunk12]
  rw [invChunk13]
  rw [invChunk14]
  rw [invChunk15]
  rw [invChunk16]
  rw [invChunk17]
  rw [invChunk18]
  rw [invChunk19]
  rw [invChunk20]
  rw [invChunk21]
  rw [invChunk22]
  rw [invChunk23]
  rw [invChunk24]
  rw [invChunk25]
  rw [invChunk26]
  rw [invChunk27]
  rw [invChunk28]
  rw [invChunk29]
  rw [invChunk30]
  rw [invChunk31]
  rw [invChunk32]
  rw [invChunk33]
  rw [invChunk34]
  rw [invChunk35]
  rw [invChunk36]
  rw [invChunk37]
  rw [invChunk38]
  rw [invChunk39]
  rw [invChunk40]
  rw [invChunk41]
  rw [invChunk42]
  rw [invChunk43]
  rw [invChunk44]
  rw [invChunk45]
  rw [invChunk46]
  rw [invChunk47]
  rw [invChunk48]
  rw [invChunk49]
  rw [invChunk50]
  rw [invChunk51]
  rw [invChunk52]
  rw [invChunk53]
  rw [invChunk54]
  rw [invChunk55]
  rw [invChunk56]
  rw [invChunk57]
  rw [invChunk58]
  rw [invChunk59]
  rw [invChunk60]
  rw [invChunk61]
  rw [invChunk62]
  rw [invChunk63]
  rw [invChunk64]
  rw [invChunk65]
  rw [invChunk66]
  rw [invChunk67]
  rw [invChunk68]
  rw [invChunk69]
  rw [invChunk70]
  rw [invChunk71]
  rw [invChunk72]
  rw [invChunk73]
  rw [invChunk74]
  rw [invChunk75]
  rw [invChunk76]
  rw [invChunk77]
  rw [invChunk78]
  rw [invChunk79]
  rw [invChunk80]
  rw [invChunk81]
  rw [invChunk82]
  rw [invChunk83]
  rw [invChunk84]
  rw [invChunk85]
  rw [invChunk86]
  rw [invChunk87]
  rw [invChunk88]
  rw [invChunk89]
  rw [invChunk90]
  rw [invChunk91]
  rw [invChunk92]
  rw [invChunk93]
  rw [invChunk94]
  rw [invChunk95]
  rw [invChunk96]
  rw [invChunk97]
  rw [invChunk98]
  rw [invChunk99]
  rw [invChunk100]
  rw [invChunk101]
  rw [invChunk102]
  rw [invChunk103]
  rw [invChunk104]
  rw [invChunk105]
  rw [invChunk106]
  rw [invChunk107]
  rw [invChunk108]
  rw [invChunk109]
  rw [invChunk110]
  rw [invChunk111]
  rw [invChunk112]
  rw [invChunk113]
  rw [invChunk114]
  rw [invChunk115]
  rw [invChunk116]
  rw [invChunk117]
  rw [invChunk118]
  rw [invChunk119]
  rw [invChunk120]
  rw [invChunk121]
  rw [invChunk122]
  rw [invChunk123]
  rw [invChunk124]
  rw [invChunk125]
  rw [invChunk126]
  rw [invChunk127]
  rw [invChunk128]
  rw [invChunk129]
  rw [invChunk130]
  rw [invChunk131]
  rw [invChunk132]
  rw [invChunk133]
  rw [invChunk134]
  rw [invChunk135]
  rw [invChunk136]
  rw [invChunk137]
  rw [invChunk138]
  rw [invChunk139]
  rw [invChunk140]
  rw [invChunk141]
  rw [invChunk142]
  rw [invChunk143]
  rw [invChunk144]
  rw [invChunk145]
  rw [invChunk146]
  rw [invChunk147]
  rw [invChunk148]
  rw [invChunk149]
  rw [invChunk150]
  rw [invChunk151]
  rw [invChunk152]
  rw [invChunk153]
  rw [invChunk154]
  rw [invChunk155]
  rw [invChunk156]
  rw [invChunk157]
  rw [invChunk158]
  rw [invChunk159]
  rw [invChunk160]
  rw [invChunk161]
  rw [invChunk162]
  rw [invChunk163]
  rw [invChunk164]
  rw [invChunk165]
  rw [invChunk166]
  rw [invChunk167]
  rw [invChunk168]
  decide


private lemma zmod_term_eq (k : ℕ) (hk : k ∈ Finset.Ico (1:ℕ) W) :
    (((D / k : ℕ) : ZMod M)) = (D : ZMod M) * (k : ZMod M)⁻¹ := by
  have hks : 1 ≤ k ∧ k < W := by simpa using hk
  have hkpos : 0 < k := by omega
  have hkle : k ≤ W - 1 := by omega
  have hnot : ¬ W ∣ k := by
    intro hd
    have hle : W ≤ k := Nat.le_of_dvd hkpos hd
    omega
  have hcopW : k.Coprime W := by
    rw [Nat.coprime_comm, Wprime.coprime_iff_not_dvd]
    exact hnot
  have hcop : k.Coprime M := by
    simpa [M] using hcopW.pow_right 3
  have hkunit : IsUnit (k : ZMod M) := by
    simpa using (ZMod.unitOfCoprime k hcop).isUnit
  have hkdvd : k ∣ D := by
    unfold D
    exact Nat.dvd_factorial hkpos hkle
  apply (IsUnit.mul_right_inj hkunit).mp
  calc
    (k : ZMod M) * ((D / k : ℕ) : ZMod M) = ((k * (D / k) : ℕ) : ZMod M) := by rw [Nat.cast_mul]
    _ = (D : ZMod M) := by rw [Nat.mul_div_cancel' hkdvd]
    _ = (k : ZMod M) * ((D : ZMod M) * (k : ZMod M)⁻¹) := by
      calc
        (D : ZMod M) = (D : ZMod M) * 1 := by rw [mul_one]
        _ = (D : ZMod M) * ((k : ZMod M) * (k : ZMod M)⁻¹) := by rw [ZMod.mul_inv_of_unit _ hkunit]
        _ = (k : ZMod M) * ((D : ZMod M) * (k : ZMod M)⁻¹) := by ring

private lemma S_zmod_zero : (S : ZMod M) = 0 := by
  unfold S
  change ((Int.castRingHom (ZMod M)) (∑ k ∈ Finset.Ico (1:ℕ) W, ((D / k : ℕ) : ℤ))) = 0
  rw [map_sum]
  simp only [map_natCast]
  calc
    (∑ k ∈ Finset.Ico (1:ℕ) W, (((D / k : ℕ) : ZMod M)))
        = ∑ k ∈ Finset.Ico (1:ℕ) W, ((D : ZMod M) * (k : ZMod M)⁻¹) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact zmod_term_eq k hk
    _ = (D : ZMod M) * (∑ k ∈ Finset.Ico (1:ℕ) W, ((k : ZMod M)⁻¹)) := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [inv_sum_zmod_zero, mul_zero]

private lemma sum_divInt_const {ι : Type} (s : Finset ι) (f : ι → ℤ) {d : ℤ} (hd : d ≠ 0) :
    (∑ x ∈ s, Rat.divInt (f x) d) = Rat.divInt (∑ x ∈ s, f x) d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      rw [Rat.divInt_add_divInt]
      · rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
        field_simp [hd]
        norm_num [Int.cast_add, Int.cast_mul, Int.cast_pow]
        ring
      · exact hd
      · exact hd

private lemma inv_eq_divD (k : ℕ) (hk : k ∈ Finset.Ico (1:ℕ) W) :
    (k : ℚ)⁻¹ = Rat.divInt (((D / k : ℕ) : ℤ)) (D : ℤ) := by
  have hks : 1 ≤ k ∧ k < W := by simpa using hk
  have hkpos : 0 < k := by omega
  have hkle : k ≤ W - 1 := by omega
  have hkdvd : k ∣ D := by
    unfold D
    exact Nat.dvd_factorial hkpos hkle
  have hDpos : 0 < D := by unfold D; exact Nat.factorial_pos _
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  rw [Rat.divInt_eq_div]
  field_simp [hkq, hDq]
  exact_mod_cast (Nat.mul_div_cancel' hkdvd).symm

private lemma harmonic_eq_S_div_D : harmonic (W - 1) = Rat.divInt S (D : ℤ) := by
  rw [harmonic_eq_sum_Icc]
  have hI : Finset.Icc (1:ℕ) (W - 1) = Finset.Ico (1:ℕ) W := by
    ext k
    simp
    norm_num [W]
    omega
  rw [hI]
  calc
    (∑ k ∈ Finset.Ico (1:ℕ) W, (k : ℚ)⁻¹)
        = ∑ k ∈ Finset.Ico (1:ℕ) W, Rat.divInt (((D / k : ℕ) : ℤ)) (D : ℤ) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact inv_eq_divD k hk
    _ = Rat.divInt (∑ k ∈ Finset.Ico (1:ℕ) W, ((D / k : ℕ) : ℤ)) (D : ℤ) := by
      apply sum_divInt_const
      have hDpos : 0 < D := by unfold D; exact Nat.factorial_pos _
      exact_mod_cast hDpos.ne'
    _ = Rat.divInt S (D : ℤ) := by rfl

private lemma W_not_dvd_D : ¬ W ∣ D := by
  unfold D
  rw [Wprime.dvd_factorial]
  norm_num [W]

private lemma W_wolstenholme : (3 : ℤ) ≤ padicValRat W (harmonic (W - 1)) := by
  haveI : Fact W.Prime := ⟨Wprime⟩
  have hHnz : harmonic (W - 1) ≠ 0 := by
    exact (harmonic_pos (by norm_num [W])).ne'
  have hDpos : 0 < D := by unfold D; exact Nat.factorial_pos _
  have hDnz : (D : ℤ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hSnz : S ≠ 0 := by
    intro hS0
    have : harmonic (W - 1) = 0 := by
      rw [harmonic_eq_S_div_D, hS0]
      exact Rat.zero_divInt (D : ℤ)
    exact hHnz this
  have hratnz : Rat.divInt S (D : ℤ) ≠ 0 := by
    rwa [Rat.divInt_ne_zero hDnz]
  have hSdvdZ : (M : ℤ) ∣ S := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd S M).mp S_zmod_zero
  have hpowdvd : ((W : ℤ) ^ 3) ∣ S := by
    simpa [M] using hSdvdZ
  have hSval : 3 ≤ padicValInt W S := by
    have h := (padicValInt_dvd_iff (p := W) (n := 3) (a := S)).mp hpowdvd
    cases h with
    | inl hz => exact (hSnz hz).elim
    | inr hv => exact hv
  have hDval : padicValInt W (D : ℤ) = 0 := by
    rw [padicValInt.of_nat, padicValNat.eq_zero_of_not_dvd W_not_dvd_D]
  rw [harmonic_eq_S_div_D]
  rw [padicValRat.defn W hratnz rfl]
  rw [← padicValInt.of_ne_one_ne_zero Wprime.ne_one hSnz]
  rw [← padicValInt.of_ne_one_ne_zero Wprime.ne_one hDnz]
  omega



private lemma mem_Uset_reflect {k : ℕ} (hk : k ∈ Uset) : N - k ∈ Uset := by
  simp [Uset, A] at hk ⊢
  constructor
  · constructor <;> omega
  · constructor
    · exact hk.2
    · omega


private lemma reflect_reflect {k : ℕ} (hk : k ∈ Uset) : N - (N - k) = k := by
  have hk' : k ≤ N := by
    simp [Uset, A] at hk
    omega
  exact Nat.sub_sub_self hk'

private lemma unit_sum_reflect :
    (∑ k ∈ Uset, (((N - k : ℕ) : ℚ)⁻¹)) = ∑ k ∈ Uset, ((k : ℚ)⁻¹) := by
  refine Finset.sum_bij' (fun k hk => N - k) (fun k hk => N - k) ?hi ?hj ?left ?right ?h
  · intro k hk; exact mem_Uset_reflect hk
  · intro k hk; exact mem_Uset_reflect hk
  · intro k hk
    exact reflect_reflect hk
  · intro k hk
    exact reflect_reflect hk
  · intro k hk
    rfl


private def Runit : ℚ := ∑ k ∈ Uset, (((k * (N - k) : ℕ) : ℚ)⁻¹)
private def Sunit : ℚ := ∑ k ∈ Uset, ((k : ℚ)⁻¹)
private def Smult : ℚ := ∑ k ∈ Mset, ((k : ℚ)⁻¹)


private lemma unit_pair_term (k : ℕ) (hk : k ∈ Uset) :
    (k : ℚ)⁻¹ + (((N - k : ℕ) : ℚ)⁻¹) = (N : ℚ) * (((k * (N - k) : ℕ) : ℚ)⁻¹) := by
  have hkpos : 0 < k := by
    simp [Uset, A] at hk
    omega
  have hnkpos : 0 < N - k := by
    simp [Uset, A] at hk
    omega
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hnkq : ((N - k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hnkpos.ne'
  have hprodq : (((k * (N - k) : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero hkpos.ne' hnkpos.ne')
  field_simp [hkq, hnkq, hprodq]
  have hk_le : k ≤ N := by
    simp [Uset, A] at hk
    omega
  norm_num [Nat.cast_mul, N, W]
  have hk_le_c : k ≤ 283686649 := by simpa [N, W] using hk_le
  have hsub : (((283686649 - k : ℕ) : ℚ)) = (283686649 : ℚ) - (k : ℚ) := by
    rw [Nat.cast_sub hk_le_c]
    norm_num
  rw [hsub]
  ring

private lemma two_mul_Sunit : 2 * Sunit = (N : ℚ) * Runit := by
  unfold Sunit Runit
  calc
    2 * (∑ k ∈ Uset, ((k : ℚ)⁻¹))
        = (∑ k ∈ Uset, ((k : ℚ)⁻¹)) + (∑ k ∈ Uset, ((k : ℚ)⁻¹)) := by ring
    _ = (∑ k ∈ Uset, ((k : ℚ)⁻¹)) + (∑ k ∈ Uset, (((N - k : ℕ) : ℚ)⁻¹)) := by rw [unit_sum_reflect]
    _ = ∑ k ∈ Uset, ((k : ℚ)⁻¹ + (((N - k : ℕ) : ℚ)⁻¹)) := by rw [Finset.sum_add_distrib]
    _ = ∑ k ∈ Uset, ((N : ℚ) * (((k * (N - k) : ℕ) : ℚ)⁻¹)) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      exact unit_pair_term k hk
    _ = (N : ℚ) * (∑ k ∈ Uset, (((k * (N - k) : ℕ) : ℚ)⁻¹)) := by
      rw [Finset.mul_sum]

private lemma padicValRat_sum_nonneg {p : ℕ} [Fact p.Prime] {s : Finset ℕ} {f : ℕ → ℚ}
    (hpos : ∀ k ∈ s, 0 ≤ f k) (hval : ∀ k ∈ s, (0 : ℤ) ≤ padicValRat p (f k)) :
    (0 : ℤ) ≤ padicValRat p (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [padicValRat.zero]
  | insert a s has ih =>
      simp only [Finset.sum_insert has, Finset.mem_insert] at hpos hval ⊢
      by_cases hzero : f a + ∑ x ∈ s, f x = 0
      · rw [hzero, padicValRat.zero]
      · have hmin := padicValRat.min_le_padicValRat_add (p := p) hzero
        have hlemin : (0 : ℤ) ≤ min (padicValRat p (f a)) (padicValRat p (∑ x ∈ s, f x)) := by
          exact le_min (hval a (Or.inl rfl)) (ih (by intro x hx; exact hpos x (Or.inr hx)) (by intro x hx; exact hval x (Or.inr hx)))
        exact le_trans hlemin hmin

private lemma Runit_val_nonneg : (0 : ℤ) ≤ padicValRat W Runit := by
  haveI : Fact W.Prime := ⟨Wprime⟩
  unfold Runit
  apply padicValRat_sum_nonneg
  · intro k hk
    positivity
  · intro k hk
    have hkU : k ∈ Uset := by simpa using hk
    have hkUs : (2 ≤ k ∧ k ≤ N - 2) ∧ ¬ W ∣ k := by
      simpa [Uset, A] using hkU
    have hnot : ¬ W ∣ k := hkUs.2
    have hnot2 : ¬ W ∣ N - k := by
      intro hd
      have hk_le_N : k ≤ N := by
        simp [Uset, A] at hkU
        omega
      have hkdiv : W ∣ k := by
        have := Nat.dvd_sub WdvdN hd
        rwa [Nat.sub_sub_self hk_le_N] at this
      exact hnot hkdiv
    have hnotprod : ¬ W ∣ k * (N - k) := by
      intro h
      exact (Wprime.dvd_mul.mp h).elim hnot hnot2
    have hvalnat : padicValNat W (k * (N - k)) = 0 := padicValNat.eq_zero_of_not_dvd hnotprod
    rw [padicValRat.inv, padicValRat.of_nat, hvalnat]
    norm_num

private lemma two_mem_Uset : 2 ∈ Uset := by
  simp [Uset, A, N, W]

private lemma Sunit_pos : 0 < Sunit := by
  unfold Sunit
  apply Finset.sum_pos'
  · intro k hk
    positivity
  · exact ⟨2, two_mem_Uset, by norm_num⟩

private lemma Runit_pos : 0 < Runit := by
  unfold Runit
  apply Finset.sum_pos'
  · intro k hk
    positivity
  · refine ⟨2, two_mem_Uset, ?_⟩
    norm_num [N, W]

private lemma Sunit_val_ge_two : (2 : ℤ) ≤ padicValRat W Sunit := by
  haveI : Fact W.Prime := ⟨Wprime⟩
  have h2nz : (2 : ℚ) ≠ 0 := by norm_num
  have hSnz : Sunit ≠ 0 := ne_of_gt Sunit_pos
  have hRnz : Runit ≠ 0 := ne_of_gt Runit_pos
  have hNnz : (N : ℚ) ≠ 0 := by norm_num [N, W]
  have hWnz : (W : ℚ) ≠ 0 := by norm_num [W]
  have hvalN : padicValRat W (N : ℚ) = 2 := by
    rw [show (N : ℚ) = (W : ℚ) ^ 2 by norm_num [N, W]]
    rw [padicValRat.pow hWnz, padicValRat.self Wprime.one_lt]
    norm_num
  have hval2 : padicValRat W (2 : ℚ) = 0 := by
    change padicValRat W ((2 : ℕ) : ℚ) = 0
    have hnot2nat : ¬ W ∣ 2 := by norm_num [W]
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnot2nat]
    norm_num
  have hmul_left : padicValRat W (2 * Sunit) = padicValRat W (2 : ℚ) + padicValRat W Sunit :=
    padicValRat.mul h2nz hSnz
  have hmul_right : padicValRat W ((N : ℚ) * Runit) = padicValRat W (N : ℚ) + padicValRat W Runit :=
    padicValRat.mul hNnz hRnz
  have hge : (2 : ℤ) ≤ padicValRat W ((N : ℚ) * Runit) := by
    have hRval := Runit_val_nonneg
    rw [hmul_right, hvalN]
    omega
  have hge2 : (2 : ℤ) ≤ padicValRat W (2 * Sunit) := by
    rwa [two_mul_Sunit]
  rw [hmul_left, hval2] at hge2
  simpa using hge2

private lemma harmonic_sub_one_eq_A :
    harmonic (N - 2) - 1 = ∑ k ∈ A, ((k : ℚ)⁻¹) := by
  have hm : 1 ≤ N - 2 := by norm_num [N, W]
  rw [harmonic_eq_sum_Icc]
  have hI : Finset.Icc 1 (N - 2) = insert 1 A := by
    ext k
    simp [A]
    omega
  rw [hI]
  rw [Finset.sum_insert]
  · norm_num
  · simp [A]

private lemma sum_A_eq_Smult_add_Sunit :
    (∑ k ∈ A, ((k : ℚ)⁻¹)) = Smult + Sunit := by
  unfold Smult Sunit Mset Uset
  have h := Finset.sum_filter_add_sum_filter_not (s := A) (p := fun k => W ∣ k) (f := fun k : ℕ => ((k : ℚ)⁻¹))
  simpa [add_comm] using h.symm

private lemma harmonic_sub_one_decomp : harmonic (N - 2) - 1 = Smult + Sunit := by
  rw [harmonic_sub_one_eq_A, sum_A_eq_Smult_add_Sunit]



private lemma Smult_eq : Smult = (W : ℚ)⁻¹ * harmonic (W - 1) := by
  have hbij :
      (∑ j ∈ Finset.Icc 1 (W - 1), (((W * j : ℕ) : ℚ)⁻¹)) = Smult := by
    unfold Smult Mset
    refine (Finset.sum_bij (fun j hj => W * j) ?hi ?hinj ?hsurj ?hterm)
    · intro j hj
      simp [A]
      simp at hj
      constructor
      · have hj1 : 1 ≤ j := hj.1
        nlinarith [Wpos]
      · constructor
        · have hjle : j ≤ W - 1 := hj.2
          have : W * j ≤ W * (W - 1) := Nat.mul_le_mul_left W hjle
          norm_num [N, W] at this ⊢
          omega
    · intro a ha b hb hab
      exact Nat.mul_left_cancel Wpos hab
    · intro k hk
      simp [A] at hk
      rcases hk.2 with ⟨j, rfl⟩
      refine ⟨j, ?_, rfl⟩
      simp
      constructor
      · by_contra hj0
        have : j = 0 := by omega
        subst j
        omega
      · have hklt : W * j < W * W := by
          have hk' : W * j ≤ N - 2 := hk.1.2
          norm_num [N, W] at hk' ⊢
          omega
        have hjlt : j < W := Nat.lt_of_mul_lt_mul_left hklt
        norm_num [W] at hjlt ⊢
        omega
    · intro j hj
      rfl
  rw [← hbij]
  rw [harmonic_eq_sum_Icc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp at hj
  have hWq : (W : ℚ) ≠ 0 := by norm_num [W]
  have hjpos : 0 < j := by omega
  have hjq : (j : ℚ) ≠ 0 := by exact_mod_cast hjpos.ne'
  field_simp [hWq, hjq]
  rw [Nat.cast_mul]

private lemma Smult_val_ge_two : (2 : ℤ) ≤ padicValRat W Smult := by
  haveI : Fact W.Prime := ⟨Wprime⟩
  rw [Smult_eq]
  have hWinv_nz : ((W : ℚ)⁻¹) ≠ 0 := by
    exact inv_ne_zero (by norm_num [W])
  have hHpos : 0 < harmonic (W - 1) := by
    apply harmonic_pos
    norm_num [W]
  have hHnz : harmonic (W - 1) ≠ 0 := ne_of_gt hHpos
  rw [padicValRat.mul hWinv_nz hHnz, padicValRat.inv, padicValRat.of_nat,
    padicValNat_self]
  have hone : (3 : ℤ) ≤ padicValRat W (harmonic (W - 1)) := W_wolstenholme
  omega


private lemma Smult_nonneg : 0 ≤ Smult := by
  unfold Smult
  exact Finset.sum_nonneg (by intro k hk; positivity)

private lemma harmonic_counter_val : (2 : ℤ) ≤ padicValRat W (harmonic (N - 2) - 1) := by
  haveI : Fact W.Prime := ⟨Wprime⟩
  rw [harmonic_sub_one_decomp]
  have hsum_ne : Smult + Sunit ≠ 0 := by
    have hpos : 0 < Smult + Sunit := add_pos_of_nonneg_of_pos Smult_nonneg Sunit_pos
    exact ne_of_gt hpos
  have hmin := padicValRat.min_le_padicValRat_add (p := W) hsum_ne
  have hlemin : (2 : ℤ) ≤ min (padicValRat W Smult) (padicValRat W Sunit) := by
    exact le_min Smult_val_ge_two Sunit_val_ge_two
  exact le_trans hlemin hmin

private lemma val_two_le_to_dvd (p : ℕ) [Fact p.Prime] (q : ℚ)
    (hval : (2:ℤ) ≤ padicValRat p (q - 1)) :
    p ^ 2 ∣ Int.natAbs (q.num - q.den) := by
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : q - 1 = (q.num - q.den : ℤ) /. (q.den : ℤ) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Rat.add_num_den q (-1))
  by_cases hdiff0 : q.num - q.den = 0
  · simp [hdiff0]
  have hne : (q.num - q.den : ℤ) /. (q.den : ℤ) ≠ 0 := by
    exact (Rat.divInt_ne_zero hd).2 hdiff0
  have hvalm : (2:ℤ) ≤ (multiplicity (p : ℤ) (q.num - q.den) : ℤ) -
      (multiplicity (p : ℤ) (q.den : ℤ) : ℤ) := by
    rw [hq] at hval
    simpa using (padicValRat.defn p hne rfl ▸ hval)
  have hmult : (2:ℤ) ≤ (multiplicity (p : ℤ) (q.num - q.den) : ℤ) := by
    have hden_nonneg : (0 : ℤ) ≤ (multiplicity (p : ℤ) (q.den : ℤ) : ℤ) := by exact_mod_cast (Nat.zero_le _)
    omega
  have hpne : p ≠ 1 := (Fact.out : Nat.Prime p).ne_one
  have hnat : 2 ≤ padicValNat p (Int.natAbs (q.num - q.den)) := by
    rw [← padicValInt]
    rw [padicValInt.of_ne_one_ne_zero hpne hdiff0]
    exact_mod_cast hmult
  rw [padicValNat_dvd_iff]
  exact Or.inr hnat

private lemma counterexample_divides : N ∣ A064169 (N - 2) := by
  haveI : Fact W.Prime := ⟨Wprime⟩
  unfold A064169
  change N ∣ Int.natAbs ((harmonic (N - 2)).num - (harmonic (N - 2)).den)
  exact (val_two_le_to_dvd W (harmonic (N - 2)) harmonic_counter_val)


/-- Disproof: the conjecture fails for `n = 16843^2`. -/
theorem oeis_64169_conjecture_0.disproof :
    ¬ (∀ (n : ℕ) (_hn : n > 2), (n ∣ A064169 (n - 2)) ↔ n.Prime) := by
  intro h
  have hc := h N (by norm_num [N, W])
  have hl : N ∣ A064169 (N - 2) := counterexample_divides
  have hp : N.Prime := hc.mp hl
  have hnp : ¬ N.Prime := by norm_num [N, W]
  exact hnp hp
