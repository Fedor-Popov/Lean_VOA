import VOA.Moonshine.MoonshineLRCommutant3

/-!
# Coordinate certificates and scalar transport for the Griess commutant
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.SpinLattice VOA.Moonshine.MonsterGriess.Visible
open VOA.Moonshine.MonsterGriess.LeechMatch
open scoped BigOperators Matrix

/-- A Golay coordinate involution that does not preserve the MOG column partition. -/
def commutF_genC : Equiv.Perm (Fin 24) where
  toFun := ![23, 1, 11, 7, 20, 8, 6, 3, 5, 22, 10, 2,
    12, 17, 14, 15, 19, 13, 18, 16, 4, 21, 9, 0]
  invFun := ![23, 1, 11, 7, 20, 8, 6, 3, 5, 22, 10, 2,
    12, 17, 14, 15, 19, 13, 18, 16, 4, 21, 9, 0]
  left_inv := by decide
  right_inv := by decide

theorem commutF_genC_code : liftGenPreservesCode commutF_genC := by
  apply commutL_preservesCode_basis <;> decide

/-- Code preservation is closed under composition. -/
theorem commutF_code_mul (σ τ : Equiv.Perm (Fin 24))
    (hσ : liftGenPreservesCode σ) (hτ : liftGenPreservesCode τ) :
    liftGenPreservesCode (σ * τ) := by
  intro x
  have he : permLin (ZMod 2) (σ * τ) x =
      permLin (ZMod 2) σ (permLin (ZMod 2) τ x) := by
    ext i
    rfl
  rw [he, hσ, hτ]

/-- A coordinate permutation whose columns are transverse to the MOG columns. -/
def commutF_transverse : Equiv.Perm (Fin 24) :=
  commutF_genC * commutL_pointPermA * commutF_genC

theorem commutF_transverse_code : liftGenPreservesCode commutF_transverse :=
  commutF_code_mul _ _
    (commutF_code_mul _ _ commutF_genC_code commutL_pointPermA_code) commutF_genC_code

/-- Every distinct pair is cross-column after one of three explicit coordinate actions. -/
theorem commutF_pair_escape : ∀ i j : Fin 24, i ≠ j →
    col i ≠ col j ∨ col (commutF_genC i) ≠ col (commutF_genC j) ∨
      col (commutF_transverse i) ≠ col (commutF_transverse j) := by decide

/-- A function constant on both column partitions is constant on all coordinates. -/
theorem commutF_transverse_constant {K : Type*} (f : Fin 24 → K)
    (hc : ∀ i j, col i = col j → f i = f j)
    (hp : ∀ i j, col i = col j → f (commutF_transverse i) =
      f (commutF_transverse j)) (i : Fin 24) : f i = f 0 := by
  have h0 : f 0 = f 0 := rfl
  have h1 : f 1 = f 0 := (hc 1 0 (by decide)).trans h0
  have h2 : f 2 = f 0 := (hc 2 0 (by decide)).trans h0
  have h3 : f 3 = f 0 := (hc 3 0 (by decide)).trans h0
  have h4 : f 4 = f 0 := (hp 19 16 (by decide)).trans h0
  have h9 : f 9 = f 0 := (hp 18 16 (by decide)).trans h0
  have h22 : f 22 = f 0 := (hp 17 16 (by decide)).trans h0
  have h15 : f 15 = f 0 := (hp 2 1 (by decide)).trans h1
  have h16 : f 16 = f 0 := (hp 0 1 (by decide)).trans h1
  have h5 : f 5 = f 0 := (hp 12 15 (by decide)).trans h2
  have h10 : f 10 = f 0 := (hp 14 15 (by decide)).trans h2
  have h21 : f 21 = f 0 := (hp 13 15 (by decide)).trans h2
  have h6 : f 6 = f 0 := (hc 6 4 (by decide)).trans h4
  have h7 : f 7 = f 0 := (hc 7 4 (by decide)).trans h4
  have h8 : f 8 = f 0 := (hc 8 9 (by decide)).trans h9
  have h11 : f 11 = f 0 := (hc 11 9 (by decide)).trans h9
  have h20 : f 20 = f 0 := (hc 20 22 (by decide)).trans h22
  have h23 : f 23 = f 0 := (hc 23 22 (by decide)).trans h22
  have h12 : f 12 = f 0 := (hc 12 15 (by decide)).trans h15
  have h13 : f 13 = f 0 := (hc 13 15 (by decide)).trans h15
  have h14 : f 14 = f 0 := (hc 14 15 (by decide)).trans h15
  have h17 : f 17 = f 0 := (hc 17 16 (by decide)).trans h16
  have h18 : f 18 = f 0 := (hc 18 16 (by decide)).trans h16
  have h19 : f 19 = f 0 := (hc 19 16 (by decide)).trans h16
  fin_cases i <;> assumption

/-- The integral lattice representative given by a short label's explicit coordinates. -/
def commutF_labelVector (l : ShortLabel) : leech.carrier :=
  leechEquiv.symm ⟨labelVec l, (labelVec_mem l).1⟩

theorem commutF_labelVector_coordinates (l : ShortLabel) :
    (leechEquiv (commutF_labelVector l) : Fin 24 → ℤ) = labelVec l := by
  exact congrArg Subtype.val (leechEquiv.apply_symm_apply _)

/-- Explicit label vectors represent the dictionary's short vectors up to sign. -/
theorem commutF_labelVector_pm (l : ShortLabel) :
    commutF_labelVector l = shortVec (labelIdx l) ∨
      commutF_labelVector l = -shortVec (labelIdx l) := by
  have hp := (Code.classOf_eq_iff (uvec_mem (labelIdx l)) (labelVec_mem l)).1
    ((MonsterGriess.classOf_uvec (labelIdx l)).trans (phi0_labelElt l))
  rcases hp with h | h
  · left
    apply eq_of_leechEquiv_coe
    rw [commutF_labelVector_coordinates, leechEquiv_shortVec, h]
  · right
    apply eq_of_leechEquiv_coe
    rw [commutF_labelVector_coordinates, leechEquiv_coe_neg, leechEquiv_shortVec, h]

/-- An explicit lattice-vector image identifies the induced permutation of short indices. -/
theorem commutF_label_index (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (l k : ShortLabel)
    (he : ι (commutF_labelVector l) = commutF_labelVector k ∨
      ι (commutF_labelVector l) = -commutF_labelVector k) :
    liftSignPerm ι hι (labelIdx l) = labelIdx k := by
  have hm : ι (commutF_labelVector l) = ι (shortVec (labelIdx l)) ∨
      ι (commutF_labelVector l) = -ι (shortVec (labelIdx l)) := by
    rcases commutF_labelVector_pm l with h | h
    · exact Or.inl (congrArg ι h)
    · exact Or.inr (by rw [h, map_neg])
  apply shortSignDictionary_griessShortSign.pm_injective
  exact liftSignPm_trans (liftSignPm_symm (liftSignPerm_spec ι hι (labelIdx l)))
    (liftSignPm_trans (liftSignPm_trans (liftSignPm_symm hm) he)
      (commutF_labelVector_pm k))

/-- A signed short-coordinate action sends a label basis vector to its image label line. -/
theorem commutF_short_action (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (l k : ShortLabel) (he : liftSignPerm ι hι (labelIdx l) = labelIdx k) :
    ∃ ε : ℚ, ε ≠ 0 ∧
      griessTrX (liftSignX ι hι (griessTrX (Xlift (labelElt l)))) =
        ε • Xlift (labelElt k) := by
  obtain ⟨ε, hε, hs⟩ := commutL_short_signed ι hι (labelIdx l)
  refine ⟨ε, by rcases hε with rfl | rfl <;> norm_num, ?_⟩
  rw [Xlift_labelElt, Xlift_labelElt]
  funext c
  obtain ⟨c, rfl⟩ := (liftSignPerm ι hι).surjective c
  by_cases hc : c = labelIdx l
  · subst c
    rw [← he]
    simpa only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one] using
      hs (Pi.single (labelIdx l) 1)
  · obtain ⟨δ, _, hd⟩ := commutL_short_signed ι hι c
    have hk : liftSignPerm ι hι c ≠ labelIdx k := by
      rw [← he]
      exact fun e => hc ((liftSignPerm ι hι).injective e)
    rw [hd]
    simp [hc, hk]

/-- The octad reached by a simple odd short vector. -/
def commutF_seedOctad : OctadWord := ⟨⟨B 0, B_mem_C 0⟩, by decide⟩

/-- The odd vector's codeword lies in the chosen complement to the all-ones word. -/
def commutF_seedCode : C₀ := ⟨⟨B 1, B_mem_C 1⟩, by decide⟩

/-- The negative coordinates in the octad image of the odd witness. -/
def commutF_seedSigns : Finset (Fin 24) := {1, 2, 3, 4}

theorem commutF_seedSigns_subset : commutF_seedSigns ⊆ octSupp commutF_seedOctad :=
  by decide

theorem commutF_seedSigns_even : Even commutF_seedSigns.card := by decide

/-- The nonmonomial generator carries this odd vector to an octad-shaped vector. -/
theorem commutF_odd_octad_coordinates :
    liftXiInt (oddMin 0 (B 1)) = vOct (B 0) commutF_seedSigns := by decide

/-- The odd witness's image has the short index of the indicated signed octad. -/
theorem commutF_seed_index :
    liftSignPerm liftXi liftXi_isometry
      (labelIdx (.inr (.inr (.inl (commutF_seedCode, 0))))) =
      labelIdx (.inr (.inr (.inr ⟨commutF_seedOctad,
        Octad.cls (octSupp commutF_seedOctad) commutF_seedSigns⟩))) := by
  apply commutF_label_index
  rcases octRep_cls commutF_seedSigns_subset commutF_seedSigns_even with he | he
  · left
    apply eq_of_leechEquiv_coe
    rw [liftXi_coordinates, commutF_labelVector_coordinates, commutF_labelVector_coordinates]
    change liftXiInt (oddMin 0 (B 1)) =
      vOct (B 0) (octRep commutF_seedOctad _)
    rw [he]
    exact commutF_odd_octad_coordinates
  · right
    apply eq_of_leechEquiv_coe
    rw [liftXi_coordinates, commutF_labelVector_coordinates, leechEquiv_coe_neg,
      commutF_labelVector_coordinates]
    change liftXiInt (oddMin 0 (B 1)) =
      -vOct (B 0) (octRep commutF_seedOctad _)
    rw [he]
    exact commutF_odd_octad_coordinates.trans (by decide)

/-- The octad witness has the common odd-line eigenvalue. -/
theorem commutF_seed_eigen (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    T (0, Xlift (rOct commutF_seedOctad commutF_seedSigns), 0) =
      commutOddScalar T 0 0 •
        ((0, Xlift (rOct commutF_seedOctad commutF_seedSigns), 0) : SpaceB) := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_xi_blocks
  obtain ⟨ε, hε, he⟩ := commutF_short_action liftXi liftXi_isometry _ _ commutF_seed_index
  change griessTrX (liftSignX liftXi liftXi_isometry
    (griessTrX (Xlift (rOdd commutF_seedCode 0)))) =
    ε • Xlift (rOctQ commutF_seedOctad _) at he
  rw [rOctQ_cls commutF_seedSigns_subset commutF_seedSigns_even] at he
  apply commutL_eigen_transport T h _ hg _ _ _ ε hε
    ((commutL_spin_odd_scalar T h).2 commutF_seedCode 0)
  rw [hb, he]
  simp only [map_zero, Matrix.mul_zero, Matrix.zero_mul, Prod.smul_mk, smul_zero]

/-- Every line in the witness octad block has the common odd-line eigenvalue. -/
theorem commutF_seed_octad_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (v : Octad.EvenQuot (octSupp commutF_seedOctad)) :
    T (tbasis (.inr (.inr (.inr ⟨commutF_seedOctad, v⟩)))) =
      commutOddScalar T 0 0 • tbasis (.inr (.inr (.inr ⟨commutF_seedOctad, v⟩))) := by
  obtain ⟨a, ha⟩ := commutB_Gmat_oct T h commutF_seedOctad
  have he := ha (Octad.cls (octSupp commutF_seedOctad) commutF_seedSigns)
  rw [tbasis_oct_cls commutF_seedSigns_subset commutF_seedSigns_even,
    commutF_seed_eigen T h] at he
  have hx := congrArg (fun u : SpaceB => u.2.1
    (labelIdx (.inr (.inr (.inr ⟨commutF_seedOctad,
      Octad.cls (octSupp commutF_seedOctad) commutF_seedSigns⟩))))) he
  have hl := Xlift_labelElt (.inr (.inr (.inr ⟨commutF_seedOctad,
    Octad.cls (octSupp commutF_seedOctad) commutF_seedSigns⟩)))
  change Xlift (rOctQ commutF_seedOctad _) = _ at hl
  rw [rOctQ_cls commutF_seedSigns_subset commutF_seedSigns_even] at hl
  simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, hl, Pi.single_eq_same,
    smul_eq_mul, mul_one] at hx
  rw [ha, ← hx]

/-- Sorted octad masks, split into small tables for kernel reduction. -/
def commutF_octadMasks : Array (Array (Fin (2 ^ 24))) := #[
  #[0xff, 0xf0f, 0xff0, 0x3333, 0x33cc, 0x3c3c, 0x3cc3, 0x5555,
    0x55aa, 0x5a5a, 0x5aa5, 0x6666, 0x6699, 0x6969, 0x6996, 0x9669,
    0x9696, 0x9966, 0x9999, 0xa55a, 0xa5a5, 0xaa55, 0xaaaa, 0xc33c,
    0xc3c3, 0xcc33, 0xcccc, 0xf00f, 0xf0f0, 0xff00, 0x3036a, 0x30395
  ],
  #[0x30c65, 0x30c9a, 0x33059, 0x330a6, 0x356c0, 0x35930, 0x3650c, 0x36a03,
    0x39503, 0x39a0c, 0x3a630, 0x3a9c0, 0x3c056, 0x3c0a9, 0x50539, 0x505c6,
    0x50a36, 0x50ac9, 0x5360a, 0x53905, 0x5506c, 0x55093, 0x563a0, 0x56c50,
    0x59350, 0x59ca0, 0x5a063, 0x5a09c, 0x5c605, 0x5c90a, 0x60653, 0x606ac
  ],
  #[0x6095c, 0x609a3, 0x63560, 0x63a90, 0x65306, 0x65c09, 0x66035, 0x660ca,
    0x6903a, 0x690c5, 0x6a309, 0x6ac06, 0x6c590, 0x6ca60, 0x9065c, 0x906a3,
    0x90953, 0x909ac, 0x93590, 0x93a60, 0x95309, 0x95c06, 0x9603a, 0x960c5,
    0x99035, 0x990ca, 0x9a306, 0x9ac09, 0x9c560, 0x9ca90, 0xa0536, 0xa05c9
  ],
  #[0xa0a39, 0xa0ac6, 0xa3605, 0xa390a, 0xa5063, 0xa509c, 0xa6350, 0xa6ca0,
    0xa93a0, 0xa9c50, 0xaa06c, 0xaa093, 0xac60a, 0xac905, 0xc0365, 0xc039a,
    0xc0c6a, 0xc0c95, 0xc3056, 0xc30a9, 0xc5630, 0xc59c0, 0xc6503, 0xc6a0c,
    0xc950c, 0xc9a03, 0xca6c0, 0xca930, 0xcc059, 0xcc0a6, 0xf000f, 0xf00f0
  ],
  #[0xf0f00, 0xff000, 0x11111e, 0x1111e1, 0x111e11, 0x11222d, 0x1122d2, 0x112d22,
    0x11444b, 0x1144b4, 0x114b44, 0x117888, 0x118788, 0x118878, 0x118887, 0x11b444,
    0x11d222, 0x11e111, 0x121274, 0x12128b, 0x121d84, 0x122147, 0x1221b8, 0x122e48,
    0x124721, 0x12482e, 0x1248d1, 0x127412, 0x12841d, 0x1284e2, 0x128b12, 0x12b821
  ],
  #[0x12d148, 0x12e284, 0x141427, 0x1414d8, 0x141b28, 0x142714, 0x14281b, 0x1428e4,
    0x144172, 0x14418d, 0x144e82, 0x147241, 0x14824e, 0x1482b1, 0x148d41, 0x14b182,
    0x14d814, 0x14e428, 0x171842, 0x172481, 0x174218, 0x178124, 0x181742, 0x18184d,
    0x1818b2, 0x182471, 0x18248e, 0x182b81, 0x184217, 0x1842e8, 0x184d18, 0x187124
  ],
  #[0x18812b, 0x1881d4, 0x188e24, 0x18b218, 0x18d481, 0x18e842, 0x1b1428, 0x1b2814,
    0x1b4182, 0x1b8241, 0x1d1284, 0x1d2148, 0x1d4821, 0x1d8412, 0x1e1111, 0x1e2222,
    0x1e4444, 0x1e8888, 0x211247, 0x2112b8, 0x211d48, 0x212174, 0x21218b, 0x212e84,
    0x214712, 0x21481d, 0x2148e2, 0x217421, 0x21842e, 0x2184d1, 0x218b21, 0x21b812
  ],
  #[0x21d184, 0x21e248, 0x22112d, 0x2211d2, 0x221e22, 0x22221e, 0x2222e1, 0x222d11,
    0x224478, 0x224487, 0x224b88, 0x227844, 0x228744, 0x22884b, 0x2288b4, 0x22b488,
    0x22d211, 0x22e122, 0x241781, 0x241871, 0x24188e, 0x24244d, 0x2424b2, 0x242b42,
    0x24422b, 0x2442d4, 0x244d24, 0x247118, 0x248117, 0x2481e8, 0x248e18, 0x24b224
  ],
  #[0x24d442, 0x24e881, 0x271414, 0x272828, 0x274141, 0x278282, 0x28141b, 0x2814e4,
    0x281b14, 0x282728, 0x282827, 0x2828d8, 0x28414e, 0x2841b1, 0x284e41, 0x287282,
    0x288272, 0x28828d, 0x288d82, 0x28b141, 0x28d828, 0x28e414, 0x2b1881, 0x2b2442,
    0x2b4224, 0x2b8118, 0x2d1122, 0x2d2211, 0x2d4488, 0x2d8844, 0x2e1248, 0x2e2184
  ],
  #[0x2e4812, 0x2e8421, 0x300359, 0x3003a6, 0x300c56, 0x300ca9, 0x30306a, 0x303095,
    0x30560c, 0x305903, 0x3065c0, 0x306a30, 0x309530, 0x309ac0, 0x30a603, 0x30a90c,
    0x30c065, 0x30c09a, 0x330033, 0x3300cc, 0x333300, 0x33cc00, 0x350660, 0x350990,
    0x356006, 0x359009, 0x36050a, 0x360a05, 0x3650a0, 0x36a050, 0x390505, 0x390a0a
  ],
  #[0x395050, 0x39a0a0, 0x3a0690, 0x3a0960, 0x3a6009, 0x3a9006, 0x3c003c, 0x3c00c3,
    0x3c3c00, 0x3cc300, 0x411472, 0x41148d, 0x411b82, 0x412741, 0x41284e, 0x4128b1,
    0x414127, 0x4141d8, 0x414e28, 0x417214, 0x41821b, 0x4182e4, 0x418d14, 0x41b128,
    0x41d841, 0x41e482, 0x421718, 0x421817, 0x4218e8, 0x42242b, 0x4224d4, 0x422b24
  ],
  #[0x42424d, 0x4242b2, 0x424d42, 0x427181, 0x428171, 0x42818e, 0x428e81, 0x42b242,
    0x42d424, 0x42e818, 0x44114b, 0x4411b4, 0x441e44, 0x442278, 0x442287, 0x442d88,
    0x44441e, 0x4444e1, 0x444b11, 0x447822, 0x448722, 0x44882d, 0x4488d2, 0x44b411,
    0x44d288, 0x44e144, 0x471221, 0x472112, 0x474884, 0x478448, 0x48122e, 0x4812d1
  ],
  #[0x481d21, 0x48211d, 0x4821e2, 0x482e12, 0x484784, 0x484874, 0x48488b, 0x487448,
    0x488447, 0x4884b8, 0x488b48, 0x48b884, 0x48d112, 0x48e221, 0x4b1144, 0x4b2288,
    0x4b4411, 0x4b8822, 0x4d1818, 0x4d2424, 0x4d4242, 0x4d8181, 0x4e1482, 0x4e2841,
    0x4e4128, 0x4e8214, 0x50056c, 0x500593, 0x500a63, 0x500a9c, 0x5036a0, 0x503950
  ],
  #[0x505039, 0x5050c6, 0x50630a, 0x506c05, 0x509305, 0x509c0a, 0x50a036, 0x50a0c9,
    0x50c650, 0x50c9a0, 0x530606, 0x530909, 0x536060, 0x539090, 0x550055, 0x5500aa,
    0x555500, 0x55aa00, 0x5603c0, 0x560c30, 0x56300c, 0x56c003, 0x590330, 0x590cc0,
    0x593003, 0x59c00c, 0x5a005a, 0x5a00a5, 0x5a5a00, 0x5aa500, 0x5c0609, 0x5c0906
  ],
  #[0x5c6090, 0x5c9060, 0x600635, 0x6006ca, 0x60093a, 0x6009c5, 0x603506, 0x603a09,
    0x605360, 0x605c90, 0x606053, 0x6060ac, 0x60905c, 0x6090a3, 0x60a390, 0x60ac60,
    0x60c509, 0x60ca06, 0x6305a0, 0x630a50, 0x63500a, 0x63a005, 0x65030c, 0x650c03,
    0x6530c0, 0x65c030, 0x660066, 0x660099, 0x666600, 0x669900, 0x690069, 0x690096
  ],
  #[0x696900, 0x699600, 0x6a0303, 0x6a0c0c, 0x6a3030, 0x6ac0c0, 0x6c0550, 0x6c0aa0,
    0x6c5005, 0x6ca00a, 0x711824, 0x712418, 0x714281, 0x718142, 0x721441, 0x722882,
    0x724114, 0x728228, 0x741212, 0x742121, 0x744848, 0x748484, 0x781188, 0x782244,
    0x784422, 0x788811, 0x811724, 0x81182b, 0x8118d4, 0x812417, 0x8124e8, 0x812b18
  ],
  #[0x814271, 0x81428e, 0x814d81, 0x817142, 0x81814d, 0x8181b2, 0x818e42, 0x81b281,
    0x81d418, 0x81e824, 0x82144e, 0x8214b1, 0x821b41, 0x822782, 0x822872, 0x82288d,
    0x82411b, 0x8241e4, 0x824e14, 0x827228, 0x828227, 0x8282d8, 0x828d28, 0x82b114,
    0x82d882, 0x82e441, 0x84121d, 0x8412e2, 0x841d12, 0x84212e, 0x8421d1, 0x842e21
  ],
  #[0x844748, 0x844847, 0x8448b8, 0x847484, 0x848474, 0x84848b, 0x848b84, 0x84b848,
    0x84d121, 0x84e212, 0x871188, 0x872244, 0x874422, 0x878811, 0x881178, 0x881187,
    0x881e88, 0x88224b, 0x8822b4, 0x882d44, 0x88442d, 0x8844d2, 0x884b22, 0x887811,
    0x888711, 0x88881e, 0x8888e1, 0x88b422, 0x88d244, 0x88e188, 0x8b1212, 0x8b2121
  ],
  #[0x8b4848, 0x8b8484, 0x8d1441, 0x8d2882, 0x8d4114, 0x8d8228, 0x8e1824, 0x8e2418,
    0x8e4281, 0x8e8142, 0x90063a, 0x9006c5, 0x900935, 0x9009ca, 0x903509, 0x903a06,
    0x905390, 0x905c60, 0x90605c, 0x9060a3, 0x909053, 0x9090ac, 0x90a360, 0x90ac90,
    0x90c506, 0x90ca09, 0x930550, 0x930aa0, 0x935005, 0x93a00a, 0x950303, 0x950c0c
  ],
  #[0x953030, 0x95c0c0, 0x960069, 0x960096, 0x966900, 0x969600, 0x990066, 0x990099,
    0x996600, 0x999900, 0x9a030c, 0x9a0c03, 0x9a30c0, 0x9ac030, 0x9c05a0, 0x9c0a50,
    0x9c500a, 0x9ca005, 0xa00563, 0xa0059c, 0xa00a6c, 0xa00a93, 0xa03650, 0xa039a0,
    0xa05036, 0xa050c9, 0xa06305, 0xa06c0a, 0xa0930a, 0xa09c05, 0xa0a039, 0xa0a0c6
  ],
  #[0xa0c6a0, 0xa0c950, 0xa30609, 0xa30906, 0xa36090, 0xa39060, 0xa5005a, 0xa500a5,
    0xa55a00, 0xa5a500, 0xa60330, 0xa60cc0, 0xa63003, 0xa6c00c, 0xa903c0, 0xa90c30,
    0xa9300c, 0xa9c003, 0xaa0055, 0xaa00aa, 0xaa5500, 0xaaaa00, 0xac0606, 0xac0909,
    0xac6060, 0xac9090, 0xb11482, 0xb12841, 0xb14128, 0xb18214, 0xb21818, 0xb22424
  ],
  #[0xb24242, 0xb28181, 0xb41144, 0xb42288, 0xb44411, 0xb48822, 0xb81221, 0xb82112,
    0xb84884, 0xb88448, 0xc00356, 0xc003a9, 0xc00c59, 0xc00ca6, 0xc03065, 0xc0309a,
    0xc05603, 0xc0590c, 0xc06530, 0xc06ac0, 0xc095c0, 0xc09a30, 0xc0a60c, 0xc0a903,
    0xc0c06a, 0xc0c095, 0xc3003c, 0xc300c3, 0xc33c00, 0xc3c300, 0xc50690, 0xc50960
  ],
  #[0xc56009, 0xc59006, 0xc60505, 0xc60a0a, 0xc65050, 0xc6a0a0, 0xc9050a, 0xc90a05,
    0xc950a0, 0xc9a050, 0xca0660, 0xca0990, 0xca6006, 0xca9009, 0xcc0033, 0xcc00cc,
    0xcc3300, 0xcccc00, 0xd11248, 0xd12184, 0xd14812, 0xd18421, 0xd21122, 0xd22211,
    0xd24488, 0xd28844, 0xd41881, 0xd42442, 0xd44224, 0xd48118, 0xd81414, 0xd82828
  ],
  #[0xd84141, 0xd88282, 0xe11111, 0xe12222, 0xe14444, 0xe18888, 0xe21284, 0xe22148,
    0xe24821, 0xe28412, 0xe41428, 0xe42814, 0xe44182, 0xe48241, 0xe81842, 0xe82481,
    0xe84218, 0xe88124, 0xf0000f, 0xf000f0, 0xf00f00, 0xf0f000, 0xff0000, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0
  ]
]

/-- Parent, generator, and breadth-first rank for each octad mask. -/
def commutF_octadLinks : Array (Array (Fin 759 × Fin 3 × ℕ)) := #[
  #[(589, 2, 658), (685, 2, 228), (410, 2, 370), (610, 1, 381), (478, 1, 200),
    (474, 1, 573), (24, 0, 672), (718, 1, 709), (306, 1, 703), (326, 1, 578),
    (698, 1, 366), (354, 2, 37), (646, 1, 713), (15, 0, 471), (430, 1, 617),
    (692, 2, 261), (421, 2, 676), (443, 1, 539), (597, 2, 245), (9, 0, 725),
    (534, 2, 206), (719, 1, 584), (357, 2, 332), (425, 2, 694), (615, 1, 477),
    (600, 2, 653), (479, 1, 630), (1, 0, 423), (127, 1, 352), (0, 1, 744),
    (324, 1, 201), (704, 1, 300)
  ],
  #[(716, 1, 124), (312, 1, 55), (664, 1, 104), (291, 0, 479), (298, 0, 111),
    (191, 2, 503), (103, 2, 430), (302, 0, 27), (595, 1, 257), (459, 1, 350),
    (71, 1, 687), (87, 1, 253), (197, 2, 642), (293, 0, 280), (652, 1, 367),
    (112, 2, 483), (447, 2, 596), (423, 0, 196), (294, 1, 567), (686, 1, 107),
    (410, 0, 368), (624, 2, 126), (34, 1, 208), (208, 2, 636), (115, 1, 355),
    (35, 1, 675), (585, 2, 72), (472, 1, 735), (419, 0, 68), (125, 2, 422),
    (624, 1, 125), (459, 0, 349)
  ],
  #[(488, 1, 734), (541, 2, 606), (100, 1, 310), (462, 0, 563), (416, 1, 437),
    (547, 2, 316), (708, 1, 405), (320, 1, 494), (316, 1, 241), (712, 1, 647),
    (709, 2, 414), (417, 1, 747), (53, 1, 252), (463, 0, 554), (439, 2, 585),
    (710, 2, 62), (625, 1, 470), (597, 0, 243), (58, 1, 150), (598, 0, 504),
    (638, 1, 240), (600, 0, 652), (586, 0, 654), (587, 0, 127), (709, 1, 413),
    (321, 1, 656), (423, 1, 197), (577, 2, 20), (107, 1, 420), (599, 0, 343),
    (135, 2, 550), (657, 1, 561)
  ],
  #[(723, 2, 219), (639, 0, 176), (634, 0, 139), (304, 1, 449), (515, 2, 158),
    (627, 0, 487), (124, 1, 464), (640, 0, 231), (631, 0, 271), (125, 1, 421),
    (43, 2, 460), (605, 2, 225), (345, 2, 9), (697, 1, 195), (686, 0, 106),
    (313, 1, 478), (325, 1, 278), (697, 0, 194), (682, 0, 496), (645, 1, 185),
    (72, 1, 443), (692, 0, 259), (556, 2, 706), (460, 1, 740), (461, 1, 681),
    (597, 1, 244), (691, 0, 328), (181, 2, 333), (684, 0, 256), (685, 0, 226),
    (757, 1, 533), (203, 2, 183)
  ],
  #[(757, 0, 532), (28, 1, 566), (130, 0, 0), (558, 2, 267), (541, 1, 605),
    (715, 2, 276), (203, 1, 182), (149, 1, 335), (679, 1, 518), (190, 2, 152),
    (385, 1, 698), (213, 1, 569), (214, 1, 475), (193, 2, 574), (723, 1, 218),
    (386, 1, 594), (150, 1, 399), (542, 1, 548), (415, 2, 400), (668, 1, 321),
    (336, 1, 559), (736, 1, 174), (260, 1, 210), (350, 2, 523), (690, 2, 453),
    (220, 0, 739), (221, 0, 473), (168, 1, 313), (217, 0, 89), (200, 1, 755),
    (223, 0, 484), (222, 0, 738)
  ],
  #[(212, 0, 488), (215, 0, 719), (336, 0, 558), (282, 1, 756), (226, 1, 137),
    (362, 1, 601), (674, 1, 692), (398, 1, 732), (330, 0, 161), (331, 0, 581),
    (130, 1, 1), (333, 0, 108), (334, 0, 556), (733, 2, 303), (559, 1, 157),
    (72, 2, 444), (363, 1, 410), (76, 2, 458), (493, 0, 363), (583, 2, 40),
    (251, 1, 446), (355, 1, 172), (192, 1, 35), (516, 0, 93), (130, 2, 2),
    (585, 1, 71), (33, 2, 117), (516, 1, 94), (733, 1, 302), (510, 0, 688),
    (520, 0, 73), (356, 1, 297)
  ],
  #[(517, 2, 15), (508, 0, 360), (357, 1, 331), (253, 1, 438), (517, 1, 14),
    (518, 0, 434), (82, 2, 292), (669, 0, 686), (145, 1, 717), (667, 0, 651),
    (723, 0, 217), (275, 1, 91), (725, 0, 752), (175, 1, 648), (738, 0, 602),
    (739, 0, 371), (740, 0, 427), (224, 1, 600), (750, 2, 147), (150, 0, 398),
    (266, 1, 283), (323, 2, 354), (659, 2, 266), (334, 1, 557), (155, 0, 524),
    (680, 2, 42), (199, 1, 749), (526, 1, 551), (274, 2, 615), (681, 2, 263),
    (753, 2, 610), (325, 2, 279)
  ],
  #[(276, 2, 389), (267, 1, 587), (744, 1, 66), (294, 2, 568), (454, 2, 495),
    (500, 1, 753), (576, 1, 133), (671, 2, 81), (288, 1, 23), (635, 2, 48),
    (217, 1, 90), (389, 1, 704), (463, 2, 555), (680, 1, 41), (303, 2, 722),
    (234, 0, 179), (231, 0, 165), (154, 1, 668), (507, 1, 75), (356, 0, 296),
    (357, 0, 330), (750, 1, 146), (178, 1, 577), (183, 1, 186), (349, 0, 499),
    (402, 1, 509), (347, 1, 727), (316, 2, 242), (730, 1, 700), (278, 1, 238),
    (244, 1, 545), (348, 1, 317)
  ],
  #[(184, 1, 7), (508, 1, 361), (371, 1, 737), (497, 0, 346), (664, 2, 105),
    (139, 1, 723), (528, 0, 467), (212, 2, 490), (490, 2, 540), (237, 1, 87),
    (643, 2, 145), (533, 0, 379), (505, 1, 708), (668, 2, 322), (740, 2, 429),
    (525, 0, 690), (493, 2, 364), (527, 0, 637), (142, 1, 407), (570, 1, 43),
    (534, 0, 204), (530, 0, 29), (673, 0, 119), (672, 0, 293), (671, 0, 80),
    (257, 1, 575), (726, 0, 733), (727, 0, 742), (223, 1, 485), (729, 0, 707),
    (276, 1, 388), (344, 1, 516)
  ],
  #[(745, 0, 10), (744, 0, 65), (34, 0, 207), (427, 1, 273), (447, 1, 595),
    (643, 1, 144), (323, 1, 353), (703, 1, 402), (38, 0, 639), (40, 0, 465),
    (232, 2, 53), (42, 0, 750), (37, 0, 693), (81, 1, 447), (745, 2, 12),
    (41, 0, 564), (32, 0, 247), (33, 0, 115), (679, 2, 519), (480, 1, 319),
    (484, 2, 436), (277, 2, 64), (486, 2, 612), (51, 1, 213), (288, 2, 24),
    (631, 1, 272), (297, 1, 662), (469, 0, 543), (466, 0, 121), (117, 1, 468),
    (695, 1, 254), (605, 0, 224)
  ],
  #[(602, 0, 287), (43, 1, 459), (644, 0, 385), (645, 0, 184), (642, 0, 100),
    (643, 0, 143), (698, 0, 365), (617, 1, 603), (17, 1, 714), (700, 0, 167),
    (182, 2, 79), (739, 1, 372), (133, 1, 481), (714, 2, 51), (97, 2, 340),
    (173, 0, 511), (566, 2, 342), (189, 2, 751), (388, 2, 527), (444, 2, 476),
    (675, 1, 683), (399, 1, 748), (194, 2, 546), (230, 1, 264), (174, 0, 306),
    (170, 0, 3), (251, 0, 445), (591, 2, 580), (280, 1, 163), (672, 1, 294),
    (404, 1, 311), (352, 1, 169)
  ],
  #[(752, 1, 83), (418, 2, 604), (256, 0, 16), (512, 1, 85), (584, 1, 153),
    (492, 1, 171), (513, 1, 432), (247, 0, 357), (353, 1, 736), (249, 1, 695),
    (678, 1, 391), (378, 1, 220), (382, 1, 562), (286, 1, 598), (722, 1, 337),
    (210, 1, 286), (170, 2, 5), (544, 2, 625), (538, 1, 514), (146, 1, 608),
    (147, 1, 534), (550, 2, 729), (202, 1, 406), (613, 2, 531), (367, 0, 492),
    (383, 1, 553), (531, 1, 110), (171, 1, 215), (339, 1, 671), (122, 2, 542),
    (497, 1, 347), (722, 2, 338)
  ],
  #[(532, 1, 463), (538, 0, 513), (30, 2, 384), (426, 2, 114), (547, 0, 314),
    (548, 0, 520), (513, 2, 433), (36, 2, 223), (518, 2, 435), (140, 2, 670),
    (273, 1, 743), (41, 2, 565), (173, 1, 512), (533, 1, 380), (397, 1, 589),
    (675, 0, 682), (553, 1, 425), (90, 2, 378), (733, 0, 301), (359, 1, 572),
    (731, 0, 159), (519, 1, 362), (144, 1, 607), (555, 2, 627), (746, 0, 304),
    (433, 2, 593), (482, 1, 192), (53, 0, 251), (58, 0, 149), (470, 1, 741),
    (30, 1, 383), (110, 1, 211)
  ],
  #[(650, 1, 237), (47, 0, 678), (290, 1, 394), (530, 2, 31), (683, 1, 203),
    (291, 1, 480), (434, 1, 646), (654, 1, 98), (111, 1, 674), (31, 1, 507),
    (312, 0, 54), (634, 1, 140), (102, 1, 661), (54, 1, 395), (720, 1, 411),
    (308, 1, 644), (3, 1, 591), (4, 1, 382), (84, 1, 440), (473, 0, 538),
    (456, 1, 616), (553, 2, 426), (74, 1, 623), (90, 1, 377), (598, 1, 505),
    (93, 2, 560), (329, 1, 323), (647, 0, 325), (649, 0, 268), (24, 1, 673),
    (704, 0, 299), (420, 1, 386)
  ],
  #[(56, 1, 570), (703, 0, 401), (70, 0, 613), (319, 1, 417), (72, 0, 442),
    (711, 1, 666), (412, 1, 288), (74, 0, 622), (96, 1, 409), (76, 0, 456),
    (62, 0, 249), (234, 2, 181), (487, 1, 619), (636, 2, 486), (497, 2, 348),
    (97, 1, 339), (640, 2, 233), (413, 1, 757), (39, 1, 58), (317, 0, 665),
    (314, 0, 745), (691, 1, 329), (487, 2, 620), (662, 2, 246), (286, 2, 599),
    (329, 2, 324), (247, 2, 359), (675, 2, 684), (9, 1, 726), (255, 2, 529),
    (654, 2, 99), (319, 2, 418)
  ],
  #[(280, 2, 164), (22, 1, 547), (601, 1, 95), (215, 2, 721), (650, 0, 236),
    (651, 0, 491), (708, 0, 404), (709, 0, 412), (693, 1, 597), (301, 1, 650),
    (351, 1, 327), (247, 1, 358), (752, 2, 84), (187, 1, 189), (260, 0, 209),
    (138, 1, 754), (370, 1, 699), (234, 1, 180), (164, 1, 270), (524, 1, 56),
    (249, 2, 696), (332, 1, 677), (554, 0, 571), (555, 0, 626), (158, 1, 679),
    (557, 0, 528), (349, 1, 500), (192, 0, 34), (183, 2, 187), (731, 1, 160),
    (279, 1, 498), (245, 1, 284)
  ],
  #[(583, 1, 39), (186, 0, 234), (564, 2, 26), (182, 0, 77), (570, 2, 44),
    (184, 0, 6), (186, 1, 235), (187, 0, 188), (196, 2, 33), (109, 2, 375),
    (6, 2, 746), (269, 0, 536), (564, 1, 25), (349, 2, 501), (149, 2, 336),
    (740, 1, 428), (595, 2, 258), (400, 1, 634), (368, 1, 13), (232, 1, 52),
    (695, 2, 255), (423, 2, 198), (233, 1, 103), (264, 0, 715), (137, 1, 295),
    (270, 0, 638), (746, 1, 305), (198, 1, 497), (396, 0, 697), (494, 1, 396),
    (578, 1, 334), (397, 0, 588)
  ],
  #[(391, 0, 415), (392, 0, 643), (169, 2, 728), (330, 1, 162), (174, 2, 308),
    (390, 0, 641), (331, 1, 582), (263, 1, 685), (384, 0, 660), (387, 0, 229),
    (115, 2, 356), (391, 1, 416), (155, 1, 525), (547, 1, 315), (289, 1, 135),
    (507, 2, 76), (331, 2, 583), (681, 1, 262), (427, 2, 274), (32, 2, 248),
    (745, 1, 11), (136, 2, 702), (156, 1, 177), (548, 1, 521), (567, 0, 705),
    (142, 2, 408), (577, 1, 19), (566, 0, 341), (563, 0, 450), (221, 1, 474),
    (679, 0, 517), (678, 0, 390)
  ],
  #[(277, 1, 63), (345, 1, 8), (736, 0, 173), (126, 2, 711), (375, 1, 710),
    (239, 1, 345), (51, 2, 214), (256, 1, 17), (520, 1, 74), (196, 1, 32),
    (411, 2, 455), (710, 1, 61), (88, 0, 621), (318, 1, 461), (84, 0, 439),
    (410, 1, 369), (82, 0, 290), (92, 0, 632), (486, 1, 611), (79, 0, 130),
    (622, 1, 664), (466, 1, 122), (356, 2, 298), (156, 2, 178), (411, 1, 454),
    (91, 0, 45), (185, 2, 148), (38, 1, 640), (690, 1, 452), (298, 1, 112),
    (590, 1, 645), (113, 2, 374)
  ],
  #[(66, 1, 522), (82, 1, 291), (478, 0, 199), (479, 0, 629), (70, 2, 614),
    (480, 0, 318), (80, 2, 667), (649, 1, 269), (400, 2, 635), (20, 1, 393),
    (464, 1, 431), (509, 2, 312), (654, 0, 97), (76, 1, 457), (40, 1, 466),
    (430, 2, 618), (710, 0, 60), (692, 1, 260), (100, 0, 309), (293, 2, 282),
    (106, 0, 657), (107, 0, 419), (494, 2, 397), (226, 2, 138), (297, 2, 663),
    (655, 1, 659), (744, 2, 67), (108, 0, 21), (293, 1, 281), (685, 1, 227),
    (673, 2, 120), (237, 2, 88)
  ],
  #[(33, 1, 116), (113, 1, 373), (635, 1, 47), (419, 1, 69), (324, 2, 202),
    (275, 2, 92), (442, 0, 537), (700, 1, 168), (5, 1, 724), (289, 2, 136),
    (499, 2, 118), (245, 2, 285), (482, 0, 191), (257, 2, 576), (91, 1, 46),
    (318, 2, 462), (278, 2, 239), (599, 1, 344), (721, 1, 277), (309, 1, 134),
    (219, 2, 718), (469, 2, 544), (716, 0, 123), (647, 2, 326), (714, 0, 49),
    (715, 0, 275), (135, 1, 549), (563, 1, 451), (231, 1, 166), (367, 1, 493),
    (295, 2, 609), (354, 1, 36)
  ],
  #[(190, 1, 151), (514, 1, 57), (243, 2, 502), (212, 1, 489), (400, 0, 633),
    (401, 0, 586), (534, 1, 205), (174, 1, 307), (577, 0, 18), (576, 0, 132),
    (412, 2, 289), (642, 1, 101), (587, 2, 129), (426, 1, 113), (714, 1, 50),
    (147, 2, 535), (586, 1, 655), (10, 2, 579), (62, 1, 250), (352, 2, 170),
    (79, 1, 131), (420, 2, 387), (451, 1, 628), (587, 1, 128), (112, 0, 482),
    (601, 2, 96), (187, 2, 190), (561, 2, 472), (11, 1, 82), (397, 2, 590),
    (446, 2, 506), (110, 2, 212)
  ],
  #[(584, 2, 154), (121, 2, 448), (543, 2, 731), (366, 2, 552), (171, 2, 216),
    (36, 1, 222), (302, 1, 28), (625, 0, 469), (84, 2, 441), (122, 1, 541),
    (108, 1, 22), (60, 1, 141), (39, 2, 59), (640, 1, 232), (613, 1, 530),
    (49, 2, 376), (378, 2, 221), (60, 2, 142), (265, 1, 175), (333, 1, 109),
    (188, 2, 510), (525, 1, 691), (3, 2, 592), (544, 1, 624), (284, 0, 680),
    (388, 1, 526), (538, 2, 515), (182, 1, 78), (346, 1, 649), (242, 1, 155),
    (372, 1, 712), (31, 2, 508)
  ],
  #[(512, 2, 86), (140, 1, 669), (678, 2, 392), (482, 2, 193), (387, 1, 230),
    (215, 1, 720), (287, 0, 701), (230, 2, 265), (530, 1, 30), (170, 1, 4),
    (242, 2, 156), (315, 2, 716), (248, 2, 689), (560, 1, 730), (585, 0, 70),
    (642, 2, 102), (583, 0, 38), (582, 0, 403), (629, 2, 631), (127, 0, 351),
    (1, 1, 424), (240, 2, 320), (283, 2, 758), (0, 0, 0), (0, 0, 0),
    (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (0, 0, 0), (0, 0, 0)
  ]
]

/-- The three explicit code-preserving coordinate generators. -/
def commutF_generator : Fin 3 → Equiv.Perm (Fin 24) :=
  ![commutL_pointPermA, commutL_pointPermB, commutF_genC]

def commutF_octadMask (i : Fin 759) : Fin (2 ^ 24) :=
  (commutF_octadMasks[i.val / 32]!)[i.val % 32]!

def commutF_octadLink (i : Fin 759) : Fin 759 × Fin 3 × ℕ :=
  (commutF_octadLinks[i.val / 32]!)[i.val % 32]!

/-- Adjacent masks increase, and each nonroot edge reduces the breadth-first rank. -/
def commutF_octadCheck (n : ℕ) : Prop :=
  if hn : n < 759 then
    let i : Fin 759 := ⟨n, hn⟩
    (∀ hs : n + 1 < 759, commutF_octadMask i < commutF_octadMask ⟨n + 1, hs⟩) ∧
    (i = 130 ∨
      (commutF_octadLink (commutF_octadLink i).1).2.2 < (commutF_octadLink i).2.2 ∧
      permLin (ZMod 2) (commutF_generator (commutF_octadLink i).2.1)
        (bvec 24 (commutF_octadMask (commutF_octadLink i).1)) =
          bvec 24 (commutF_octadMask i))
  else True

private theorem commutF_octadCheck00 :
    ∀ j : Fin 32, commutF_octadCheck (0 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck01 :
    ∀ j : Fin 32, commutF_octadCheck (1 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck02 :
    ∀ j : Fin 32, commutF_octadCheck (2 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck03 :
    ∀ j : Fin 32, commutF_octadCheck (3 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck04 :
    ∀ j : Fin 32, commutF_octadCheck (4 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck05 :
    ∀ j : Fin 32, commutF_octadCheck (5 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck06 :
    ∀ j : Fin 32, commutF_octadCheck (6 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck07 :
    ∀ j : Fin 32, commutF_octadCheck (7 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck08 :
    ∀ j : Fin 32, commutF_octadCheck (8 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck09 :
    ∀ j : Fin 32, commutF_octadCheck (9 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck10 :
    ∀ j : Fin 32, commutF_octadCheck (10 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck11 :
    ∀ j : Fin 32, commutF_octadCheck (11 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck12 :
    ∀ j : Fin 32, commutF_octadCheck (12 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck13 :
    ∀ j : Fin 32, commutF_octadCheck (13 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck14 :
    ∀ j : Fin 32, commutF_octadCheck (14 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck15 :
    ∀ j : Fin 32, commutF_octadCheck (15 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck16 :
    ∀ j : Fin 32, commutF_octadCheck (16 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck17 :
    ∀ j : Fin 32, commutF_octadCheck (17 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck18 :
    ∀ j : Fin 32, commutF_octadCheck (18 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck19 :
    ∀ j : Fin 32, commutF_octadCheck (19 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck20 :
    ∀ j : Fin 32, commutF_octadCheck (20 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck21 :
    ∀ j : Fin 32, commutF_octadCheck (21 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck22 :
    ∀ j : Fin 32, commutF_octadCheck (22 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

private theorem commutF_octadCheck23 :
    ∀ j : Fin 32, commutF_octadCheck (23 * 32 + j.val) := by
  unfold commutF_octadCheck
  decide

theorem commutF_octadCheck_all (i : Fin 759) : commutF_octadCheck i.val := by
  have hb : i.val / 32 < 24 := by omega
  have hj : i.val % 32 < 32 := Nat.mod_lt _ (by decide)
  have hall : ∀ b : Fin 24, ∀ j : Fin 32, commutF_octadCheck (b.val * 32 + j.val) := by
    intro b
    fin_cases b
    · exact commutF_octadCheck00
    · exact commutF_octadCheck01
    · exact commutF_octadCheck02
    · exact commutF_octadCheck03
    · exact commutF_octadCheck04
    · exact commutF_octadCheck05
    · exact commutF_octadCheck06
    · exact commutF_octadCheck07
    · exact commutF_octadCheck08
    · exact commutF_octadCheck09
    · exact commutF_octadCheck10
    · exact commutF_octadCheck11
    · exact commutF_octadCheck12
    · exact commutF_octadCheck13
    · exact commutF_octadCheck14
    · exact commutF_octadCheck15
    · exact commutF_octadCheck16
    · exact commutF_octadCheck17
    · exact commutF_octadCheck18
    · exact commutF_octadCheck19
    · exact commutF_octadCheck20
    · exact commutF_octadCheck21
    · exact commutF_octadCheck22
    · exact commutF_octadCheck23
  have he : i.val / 32 * 32 + i.val % 32 = i.val := by omega
  simpa only [he] using hall ⟨i.val / 32, hb⟩ ⟨i.val % 32, hj⟩

/-- The mask table has no repetitions. -/
theorem commutF_octadMask_strictMono : StrictMono commutF_octadMask := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hc := commutF_octadCheck_all i.castSucc
  simp only [commutF_octadCheck, dif_pos i.castSucc.isLt] at hc
  exact hc.1 (Nat.succ_lt_succ i.isLt)

/-- A predicate propagated by the three generators holds at every certified octad. -/
theorem commutF_octad_tree (P : (Fin 24 → ZMod 2) → Prop) (h0 : P (B 0))
    (hg : ∀ g : Fin 3, ∀ x, P x → P (permLin (ZMod 2) (commutF_generator g) x))
    (i : Fin 759) : P (bvec 24 (commutF_octadMask i)) := by
  have hall : ∀ n : ℕ, ∀ j : Fin 759, (commutF_octadLink j).2.2 = n →
      P (bvec 24 (commutF_octadMask j)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      have hc := commutF_octadCheck_all j
      simp only [commutF_octadCheck, dif_pos j.isLt] at hc
      rcases hc.2 with hr | ⟨hp, he⟩
      · change j = 130 at hr
        rw [hr]
        have he : bvec 24 (commutF_octadMask 130) = B 0 := by decide
        rwa [he]
      · rw [← he]
        exact hg _ _ (ih _ (hp.trans_eq hj) _ rfl)
  exact hall _ i rfl

/-- Every certified coordinate generator preserves the Golay code. -/
theorem commutF_generator_code (g : Fin 3) :
    liftGenPreservesCode (commutF_generator g) := by
  fin_cases g
  · exact commutL_pointPermA_code
  · exact commutL_pointPermB_code
  · exact commutF_genC_code

/-- Coordinate permutations preserve Hamming weight. -/
theorem commutF_perm_weight (σ : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    hammingNorm (permLin (ZMod 2) σ x) = hammingNorm x := by
  rw [hammingNorm_eq_sum_val, hammingNorm_eq_sum_val]
  exact Equiv.sum_comp σ.symm (fun i => (x i).val)

/-- Every mask in the spanning tree is an octad codeword. -/
theorem commutF_octad_valid (i : Fin 759) :
    bvec 24 (commutF_octadMask i) ∈ Code.C ∧
      hammingNorm (bvec 24 (commutF_octadMask i)) = 8 := by
  apply commutF_octad_tree (fun x => x ∈ Code.C ∧ hammingNorm x = 8)
    ⟨B_mem_C 0, by decide⟩
  intro g x hx
  exact ⟨(commutF_generator_code g x).mpr hx.1,
    (commutF_perm_weight _ x).trans hx.2⟩

/-- Binary vectors distinguish masks smaller than two to the coordinate dimension. -/
theorem commutF_bvec_injective :
    Function.Injective (fun a : Fin (2 ^ 24) => bvec 24 a.val) := by
  intro a b hab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 24
  · have he := congrFun hab ⟨j, hj⟩
    change (if a.val.testBit j then (1 : ZMod 2) else 0) =
      (if b.val.testBit j then 1 else 0) at he
    cases ha : a.val.testBit j <;> cases hb : b.val.testBit j <;>
      simp_all
  · have hp : 2 ^ 24 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (a.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (b.isLt.trans_le hp)]

/-- The certified table, interpreted as octads. -/
def commutF_octadEnum (i : Fin 759) : OctadWord :=
  ⟨⟨bvec 24 (commutF_octadMask i), (commutF_octad_valid i).1⟩,
    (commutF_octad_valid i).2⟩

/-- The certified table exhausts all octads, using the proved octad count. -/
theorem commutF_octadEnum_surjective : Function.Surjective commutF_octadEnum := by
  apply ((Fintype.bijective_iff_injective_and_card commutF_octadEnum).mpr ⟨?_, ?_⟩).2
  · intro i j he
    apply commutF_octadMask_strictMono.injective
    apply commutF_bvec_injective
    exact congrArg (fun o : OctadWord => o.val.val) he
  · rw [Fintype.card_fin, card_octadWord]

/-- A predicate true on the witness and preserved by the generators holds on every octad. -/
theorem commutF_octad_transitive (P : (Fin 24 → ZMod 2) → Prop) (h0 : P (B 0))
    (hg : ∀ g : Fin 3, ∀ x, P x → P (permLin (ZMod 2) (commutF_generator g) x))
    (o : OctadWord) : P o.val.val := by
  obtain ⟨i, rfl⟩ := commutF_octadEnum_surjective o
  exact commutF_octad_tree P h0 hg i

/-- A code-preserving coordinate permutation acts on octad words. -/
def commutF_octadPerm (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ)
    (o : OctadWord) : OctadWord :=
  ⟨⟨permLin (ZMod 2) σ o.val.val, (hσ _).mpr o.val.property⟩,
    (commutF_perm_weight σ o.val.val).trans o.property⟩

/-- The empty-sign octad label represents the all-positive octad vector up to sign. -/
theorem commutF_octad_empty_label (o : OctadWord) :
    labelVec (.inr (.inr (.inr ⟨o, Octad.cls (octSupp o) ∅⟩))) = vOct o.val.val ∅ ∨
      labelVec (.inr (.inr (.inr ⟨o, Octad.cls (octSupp o) ∅⟩))) = -vOct o.val.val ∅ := by
  have hs : (∅ : Finset (Fin 24)) ⊆ octSupp o := Finset.empty_subset _
  have he : Even (∅ : Finset (Fin 24)).card := by decide
  rcases octRep_cls hs he with hp | hp
  · left
    change vOct o.val.val (octRep o _) = _
    rw [hp]
  · right
    change vOct o.val.val (octRep o _) = _
    rw [hp]
    exact (neg_vOct hs).symm

/-- Coordinate permutations send the empty-sign octad line to the image octad line. -/
theorem commutF_octad_index (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ)
    (o : OctadWord) :
    liftSignPerm (liftGenMathieu σ hσ) (liftGenMathieu_isometry σ hσ)
      (labelIdx (.inr (.inr (.inr ⟨o, Octad.cls (octSupp o) ∅⟩)))) =
      labelIdx (.inr (.inr (.inr ⟨commutF_octadPerm σ hσ o,
        Octad.cls (octSupp (commutF_octadPerm σ hσ o)) ∅⟩))) := by
  have hv : permLin ℤ σ (vOct o.val.val ∅) =
      vOct (commutF_octadPerm σ hσ o).val.val ∅ := by
    ext i
    simp only [vOct, permLin_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      liftℤ, Octad.ind, Finset.notMem_empty, ite_false]
    rfl
  have hm : permLin ℤ σ
      (labelVec (.inr (.inr (.inr ⟨o, Octad.cls (octSupp o) ∅⟩)))) =
      labelVec (.inr (.inr (.inr ⟨commutF_octadPerm σ hσ o,
        Octad.cls (octSupp (commutF_octadPerm σ hσ o)) ∅⟩))) ∨
      permLin ℤ σ (labelVec (.inr (.inr (.inr ⟨o, Octad.cls (octSupp o) ∅⟩)))) =
      -labelVec (.inr (.inr (.inr ⟨commutF_octadPerm σ hσ o,
        Octad.cls (octSupp (commutF_octadPerm σ hσ o)) ∅⟩))) := by
    rcases commutF_octad_empty_label o with hs | hs <;>
      rcases commutF_octad_empty_label (commutF_octadPerm σ hσ o) with ht | ht
    · exact Or.inl (by rw [hs, ht, hv])
    · exact Or.inr (by rw [hs, ht, neg_neg, hv])
    · exact Or.inr (by rw [hs, map_neg, ht, hv])
    · exact Or.inl (by rw [hs, map_neg, ht, hv])
  apply commutF_label_index
  rcases hm with hm | hm
  · left
    apply eq_of_leechEquiv_coe
    rw [liftGenMathieu_coordinates, commutF_labelVector_coordinates,
      commutF_labelVector_coordinates]
    exact hm
  · right
    apply eq_of_leechEquiv_coe
    rw [liftGenMathieu_coordinates, commutF_labelVector_coordinates,
      leechEquiv_coe_neg, commutF_labelVector_coordinates]
    exact hm

/-- A nonzero label basis vector determines its scalar uniquely. -/
theorem commutF_label_scalar_unique (l : ShortLabel) (a b : ℚ)
    (he : a • ((0, Xlift (labelElt l), 0) : SpaceB) =
      b • ((0, Xlift (labelElt l), 0) : SpaceB)) : a = b := by
  have hc := congrArg (fun u : SpaceB => u.2.1 (labelIdx l)) he
  simpa only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, Xlift_labelElt,
    Pi.single_eq_same, smul_eq_mul, mul_one] using hc

/-- One octad eigenline determines the scalar on its entire block. -/
theorem commutF_octad_extend (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (o : OctadWord) (a : ℚ) (v : Octad.EvenQuot (octSupp o))
    (hv : T (tbasis (.inr (.inr (.inr ⟨o, v⟩)))) =
      a • tbasis (.inr (.inr (.inr ⟨o, v⟩))))
    (w : Octad.EvenQuot (octSupp o)) :
    T (tbasis (.inr (.inr (.inr ⟨o, w⟩)))) =
      a • tbasis (.inr (.inr (.inr ⟨o, w⟩))) := by
  obtain ⟨b, hb⟩ := commutB_Gmat_oct T h o
  have he := (hb v).symm.trans hv
  simp only [tbasis_oct] at he
  have hab := commutF_label_scalar_unique (.inr (.inr (.inr ⟨o, v⟩))) b a he
  rw [hb, hab]

/-- The scalar of an octad block propagates along every code-preserving permutation. -/
theorem commutF_octad_eigen_perm (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) (o : OctadWord) (a : ℚ)
    (ho : ∀ v : Octad.EvenQuot (octSupp o),
      T (tbasis (.inr (.inr (.inr ⟨o, v⟩)))) =
        a • tbasis (.inr (.inr (.inr ⟨o, v⟩))))
    (w : Octad.EvenQuot (octSupp (commutF_octadPerm σ hσ o))) :
    T (tbasis (.inr (.inr (.inr ⟨commutF_octadPerm σ hσ o, w⟩)))) =
      a • tbasis (.inr (.inr (.inr ⟨commutF_octadPerm σ hσ o, w⟩))) := by
  let l : ShortLabel := .inr (.inr (.inr ⟨o, Octad.cls (octSupp o) ∅⟩))
  let k : ShortLabel := .inr (.inr (.inr ⟨commutF_octadPerm σ hσ o,
    Octad.cls (octSupp (commutF_octadPerm σ hσ o)) ∅⟩))
  obtain ⟨g, _, _, hg, hb⟩ := commutL_mathieu_blocks σ hσ
  obtain ⟨ε, hε, he⟩ := commutF_short_action _ _ l k (commutF_octad_index σ hσ o)
  have hv : T (0, Xlift (labelElt l), 0) =
      a • ((0, Xlift (labelElt l), 0) : SpaceB) := by
    simpa only [tbasis_oct] using ho (Octad.cls (octSupp o) ∅)
  have hvw : ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) (0, Xlift (labelElt l), 0) =
      ε • ((0, Xlift (labelElt k), 0) : SpaceB) := by
    rw [hb, he]
    simp only [map_zero, Matrix.mul_zero, Matrix.zero_mul, Prod.smul_mk, smul_zero]
  have ht := commutL_eigen_transport T h _ hg _ _ a ε hε hv hvw
  apply commutF_octad_extend T h _ a (Octad.cls _ ∅) _ w
  simpa only [tbasis_oct] using ht

/-- Every octad block has the common odd-line eigenvalue. -/
theorem commutF_octads_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (o : OctadWord) (v : Octad.EvenQuot (octSupp o)) :
    T (tbasis (.inr (.inr (.inr ⟨o, v⟩)))) =
      commutOddScalar T 0 0 • tbasis (.inr (.inr (.inr ⟨o, v⟩))) := by
  let P (x : Fin 24 → ZMod 2) : Prop := ∃ o : OctadWord, o.val.val = x ∧
    ∀ w : Octad.EvenQuot (octSupp o), T (tbasis (.inr (.inr (.inr ⟨o, w⟩)))) =
      commutOddScalar T 0 0 • tbasis (.inr (.inr (.inr ⟨o, w⟩)))
  have h0 : P (B 0) := ⟨commutF_seedOctad, rfl, commutF_seed_octad_scalar T h⟩
  have hg (g : Fin 3) (x : Fin 24 → ZMod 2) (hx : P x) :
      P (permLin (ZMod 2) (commutF_generator g) x) := by
    obtain ⟨o, rfl, ho⟩ := hx
    exact ⟨commutF_octadPerm _ (commutF_generator_code g) o, rfl,
      commutF_octad_eigen_perm T h _ (commutF_generator_code g) o _ ho⟩
  obtain ⟨o', he, ho⟩ := commutF_octad_transitive P h0 hg o
  have he' : o' = o := Subtype.ext (Subtype.ext he)
  subst o'
  exact ho v

/-- The octad consisting of the first two MOG columns. -/
def commutF_pairOctad : OctadWord :=
  ⟨⟨B 0 + B 1, Code.C.add_mem (B_mem_C 0) (B_mem_C 1)⟩, by decide⟩

def commutF_pairSigns : Finset (Fin 24) := {0, 1, 2, 3}

theorem commutF_pairSigns_subset : commutF_pairSigns ⊆ octSupp commutF_pairOctad :=
  by decide

theorem commutF_pairSigns_even : Even commutF_pairSigns.card := by decide

/-- A cross-column pair is carried to a two-column octad. -/
theorem commutF_pair_octad_coordinates :
    liftXiInt (vMinus 0 4) = vOct commutF_pairOctad.val.val commutF_pairSigns := by
  decide

/-- The cross-column pair witness has the indicated octad image index. -/
theorem commutF_pair_index :
    liftSignPerm liftXi liftXi_isometry (labelIdx (.inl ⟨(0, 4), by decide⟩)) =
      labelIdx (.inr (.inr (.inr ⟨commutF_pairOctad,
        Octad.cls (octSupp commutF_pairOctad) commutF_pairSigns⟩))) := by
  apply commutF_label_index
  rcases octRep_cls commutF_pairSigns_subset commutF_pairSigns_even with he | he
  · left
    apply eq_of_leechEquiv_coe
    rw [liftXi_coordinates, commutF_labelVector_coordinates, commutF_labelVector_coordinates]
    change liftXiInt (vMinus 0 4) = vOct commutF_pairOctad.val.val (octRep _ _)
    rw [he]
    exact commutF_pair_octad_coordinates
  · right
    apply eq_of_leechEquiv_coe
    rw [liftXi_coordinates, commutF_labelVector_coordinates, leechEquiv_coe_neg,
      commutF_labelVector_coordinates]
    change liftXiInt (vMinus 0 4) = -vOct commutF_pairOctad.val.val (octRep _ _)
    rw [he]
    exact commutF_pair_octad_coordinates.trans (by decide)

/-- Scalar eigenvectors also transport backwards through an invertible commuting action. -/
theorem commutF_eigen_transport_back (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (g : SpaceB ≃ₗ[ℚ] SpaceB) (hg : g ∈ Generated.Gmat)
    (v w : SpaceB) (a ε : ℚ) (hw : T w = a • w) (he : g v = ε • w) :
    T v = a • v := by
  apply g.injective
  rw [← h g hg, he, map_smul, hw, map_smul, he, smul_comm]

/-- The cross-column minus line has the common odd-line scalar. -/
theorem commutF_pair_seed_short (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    T (0, Xlift (rMinus 0 4), 0) =
      commutOddScalar T 0 0 • ((0, Xlift (rMinus 0 4), 0) : SpaceB) := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_xi_blocks
  obtain ⟨ε, _, he⟩ := commutF_short_action _ _ _ _ commutF_pair_index
  change griessTrX (liftSignX liftXi liftXi_isometry
    (griessTrX (Xlift (rMinus 0 4)))) = ε • Xlift (rOctQ commutF_pairOctad _) at he
  have hw := commutF_octads_scalar T h commutF_pairOctad
    (Octad.cls (octSupp commutF_pairOctad) commutF_pairSigns)
  rw [tbasis_oct] at hw
  apply commutF_eigen_transport_back T h _ hg _ _ _ ε hw
  rw [hb, he]
  simp only [map_zero, Matrix.mul_zero, Matrix.zero_mul, Prod.smul_mk, smul_zero]

/-- The cross-column matrix witness has the common odd-line scalar. -/
theorem commutF_pair_seed_matrix (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    T (basisA s(0, 4), 0, 0) =
      commutOddScalar T 0 0 • ((basisA s(0, 4), 0, 0) : SpaceB) := by
  obtain ⟨a, hA, hm, _⟩ := commutB_pair_lines T
    (fun r => h _ (commutRho_mem_Gmat r)) (h _ commutTau_mem_Gmat) ⟨(0, 4), by decide⟩
  have he := hm.symm.trans (commutF_pair_seed_short T h)
  have ha := commutF_label_scalar_unique (.inl ⟨(0, 4), by decide⟩) a _ he
  rw [hA, ha]

/-- Congruence by a coordinate permutation permutes the symmetric matrix units. -/
theorem commutF_basisA_perm (σ : Equiv.Perm (Fin 24)) (i j : Fin 24) :
    thetaA (σ.permMatrix ℚ) (basisA s(i, j)) = basisA s(σ i, σ j) := by
  apply Subtype.ext
  ext k l
  simp only [coe_thetaA, Matrix.transpose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply,
    id_eq, basisA_apply]
  congr 1
  simp only [Sym2.eq_iff, Equiv.Perm.inv_def, Equiv.symm_apply_eq]

/-- Matrix-unit eigenvectors transport along code-preserving coordinate permutations. -/
theorem commutF_pair_matrix_perm (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ)
    (i j : Fin 24) (a : ℚ)
    (hv : T (basisA s(i, j), 0, 0) = a • ((basisA s(i, j), 0, 0) : SpaceB)) :
    T (basisA s(σ i, σ j), 0, 0) = a • ((basisA s(σ i, σ j), 0, 0) : SpaceB) := by
  obtain ⟨g, _, _, hg, hb⟩ := commutL_mathieu_blocks σ hσ
  apply commutL_eigen_transport T h _ hg _ _ a 1 one_ne_zero hv
  rw [hb, commutF_basisA_perm]
  simp only [commutL_short_zero, Matrix.mul_zero, Matrix.zero_mul, one_smul]

/-- Sorted pair codes, split into small tables for kernel reduction. -/
def commutF_pairMasks : Array (Array (Fin 576)) := #[
  #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 31, 32, 33, 34
  ],
  #[35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 51, 52, 53,
    54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69
  ],
  #[70, 71, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89,
    90, 91, 92, 93, 94, 95, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110
  ],
  #[111, 112, 113, 114, 115, 116, 117, 118, 119, 126, 127, 128, 129, 130, 131, 132,
    133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 151, 152, 153, 154, 155
  ],
  #[156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 176, 177, 178, 179,
    180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 201, 202, 203, 204
  ],
  #[205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 226, 227, 228, 229, 230,
    231, 232, 233, 234, 235, 236, 237, 238, 239, 251, 252, 253, 254, 255, 256, 257
  ],
  #[258, 259, 260, 261, 262, 263, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285,
    286, 287, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 326, 327, 328
  ],
  #[329, 330, 331, 332, 333, 334, 335, 351, 352, 353, 354, 355, 356, 357, 358, 359,
    376, 377, 378, 379, 380, 381, 382, 383, 401, 402, 403, 404, 405, 406, 407, 426
  ],
  #[427, 428, 429, 430, 431, 451, 452, 453, 454, 455, 476, 477, 478, 479, 501, 502,
    503, 526, 527, 551, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
]

/-- Parent, generator, and breadth-first rank for each pair. -/
def commutF_pairLinks : Array (Array (Fin 276 × Fin 3 × ℕ)) := #[
  #[(272, 1, 7), (275, 1, 235), (155, 2, 254), (3, 0, 0), (260, 1, 72),
    (269, 1, 271), (254, 1, 258), (11, 0, 85), (12, 0, 129), (44, 1, 32),
    (65, 1, 255), (220, 2, 46), (260, 2, 73), (9, 0, 60), (247, 2, 246),
    (230, 1, 175), (230, 2, 176), (265, 2, 18), (22, 0, 186), (170, 1, 112),
    (16, 0, 243), (17, 0, 35), (197, 1, 113), (271, 1, 78), (270, 1, 272),
    (41, 2, 178), (257, 1, 10), (266, 1, 263), (251, 1, 267), (26, 2, 21),
    (82, 1, 87), (41, 1, 177)
  ],
  #[(23, 2, 135), (29, 0, 39), (136, 1, 143), (101, 1, 162), (32, 0, 210),
    (40, 2, 59), (236, 1, 124), (217, 1, 158), (44, 0, 31), (37, 0, 107),
    (206, 1, 195), (30, 2, 151), (0, 2, 16), (273, 1, 164), (206, 2, 196),
    (259, 1, 172), (268, 1, 33), (253, 1, 169), (21, 1, 67), (84, 1, 265),
    (185, 2, 209), (64, 1, 166), (121, 1, 91), (138, 1, 270), (52, 0, 260),
    (154, 1, 118), (205, 2, 251), (238, 1, 76), (219, 1, 159), (246, 1, 127),
    (169, 1, 256), (59, 0, 132)
  ],
  #[(172, 2, 98), (61, 0, 200), (263, 1, 240), (258, 1, 248), (123, 2, 29),
    (252, 1, 19), (74, 0, 155), (154, 2, 119), (142, 2, 181), (63, 1, 205),
    (120, 1, 90), (149, 2, 81), (146, 2, 245), (153, 1, 136), (82, 0, 86),
    (83, 0, 213), (150, 2, 191), (148, 2, 274), (168, 1, 47), (153, 2, 137),
    (141, 2, 223), (195, 1, 262), (255, 1, 103), (136, 2, 144), (82, 2, 88),
    (17, 1, 36), (94, 0, 22), (194, 2, 75), (60, 1, 234), (117, 1, 50),
    (257, 2, 11), (236, 2, 125)
  ],
  #[(150, 1, 190), (101, 0, 161), (227, 2, 116), (262, 2, 238), (104, 0, 204),
    (165, 1, 95), (98, 0, 189), (179, 1, 232), (192, 1, 131), (256, 1, 266),
    (70, 2, 230), (111, 0, 226), (112, 0, 215), (113, 0, 12), (50, 2, 121),
    (116, 1, 153), (133, 1, 140), (161, 2, 5), (149, 1, 80), (166, 2, 84),
    (120, 0, 89), (214, 1, 26), (241, 1, 100), (89, 2, 70), (168, 2, 48),
    (117, 0, 49), (7, 2, 147), (250, 1, 14), (128, 0, 237), (129, 0, 216),
    (40, 1, 58), (48, 2, 64)
  ],
  #[(118, 1, 167), (133, 2, 141), (126, 0, 105), (127, 0, 114), (136, 0, 142),
    (235, 1, 82), (216, 1, 184), (132, 2, 219), (166, 1, 83), (133, 0, 139),
    (180, 1, 239), (193, 1, 247), (144, 0, 221), (78, 1, 148), (37, 1, 108),
    (45, 2, 236), (115, 1, 145), (132, 1, 218), (142, 0, 179), (77, 2, 212),
    (152, 0, 257), (232, 1, 43), (154, 0, 117), (78, 2, 149), (163, 1, 203),
    (149, 0, 79), (177, 1, 66), (190, 1, 198), (210, 0, 52), (0, 1, 15),
    (47, 2, 241), (4, 1, 128)
  ],
  #[(116, 2, 154), (3, 1, 1), (114, 2, 138), (12, 1, 130), (13, 1, 109),
    (117, 2, 51), (220, 0, 45), (7, 1, 146), (214, 0, 25), (8, 1, 202),
    (9, 1, 61), (196, 2, 224), (222, 0, 54), (219, 2, 160), (68, 1, 56),
    (238, 2, 77), (69, 1, 37), (268, 2, 34), (228, 0, 187), (74, 1, 156),
    (253, 2, 170), (70, 1, 229), (273, 2, 165), (225, 0, 173), (21, 2, 68),
    (23, 1, 134), (161, 0, 3), (175, 0, 133), (25, 1, 244), (200, 0, 273),
    (236, 0, 123), (187, 2, 207)
  ],
  #[(33, 1, 74), (239, 0, 183), (29, 1, 40), (32, 1, 211), (30, 1, 150),
    (9, 2, 62), (54, 2, 157), (48, 1, 63), (46, 1, 253), (57, 2, 193),
    (61, 2, 201), (56, 1, 275), (246, 0, 126), (57, 1, 192), (50, 1, 120),
    (241, 0, 99), (242, 0, 264), (52, 1, 261), (214, 2, 27), (157, 0, 30),
    (106, 1, 268), (216, 2, 185), (113, 1, 13), (111, 1, 227), (170, 0, 111),
    (93, 2, 93), (164, 0, 182), (165, 0, 94), (109, 1, 24), (87, 1, 220),
    (123, 1, 28), (129, 1, 217)
  ],
  #[(130, 1, 174), (255, 2, 104), (184, 0, 122), (177, 0, 65), (127, 1, 115),
    (179, 0, 231), (126, 1, 106), (88, 1, 152), (94, 1, 23), (95, 1, 199),
    (93, 1, 92), (232, 2, 44), (89, 1, 69), (191, 0, 259), (90, 1, 41),
    (13, 2, 110), (206, 0, 194), (222, 2, 55), (144, 1, 222), (240, 2, 252),
    (96, 2, 250), (143, 1, 269), (176, 2, 71), (142, 1, 180), (226, 2, 197),
    (210, 1, 53), (272, 0, 6), (160, 1, 228), (257, 0, 9), (174, 1, 101),
    (187, 1, 206), (211, 1, 57)
  ],
  #[(231, 1, 225), (161, 1, 4), (228, 2, 188), (174, 2, 102), (267, 0, 38),
    (249, 2, 96), (253, 0, 168), (259, 0, 171), (179, 2, 233), (186, 1, 8),
    (162, 1, 214), (252, 2, 20), (265, 0, 17), (15, 2, 242), (102, 2, 249),
    (90, 2, 42), (3, 2, 2), (172, 1, 97), (185, 1, 208), (261, 0, 163),
    (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0),
    (0, 0, 0), (0, 0, 0)
  ]
]

def commutF_pairMask (i : Fin 276) : Fin 576 :=
  (commutF_pairMasks[i.val / 32]!)[i.val % 32]!

def commutF_pairLink (i : Fin 276) : Fin 276 × Fin 3 × ℕ :=
  (commutF_pairLinks[i.val / 32]!)[i.val % 32]!

def commutF_pairFirst (i : Fin 276) : Fin 24 :=
  ⟨(commutF_pairMask i).val / 24, by have := (commutF_pairMask i).isLt; omega⟩

def commutF_pairSecond (i : Fin 276) : Fin 24 :=
  ⟨(commutF_pairMask i).val % 24, Nat.mod_lt _ (by decide)⟩

/-- Pair ordering, distinct masks, and rank-decreasing generator edges. -/
def commutF_pairCheck (n : ℕ) : Prop :=
  if hn : n < 276 then
    let i : Fin 276 := ⟨n, hn⟩
    commutF_pairFirst i < commutF_pairSecond i ∧
    (∀ hs : n + 1 < 276, commutF_pairMask i < commutF_pairMask ⟨n + 1, hs⟩) ∧
    (i = 3 ∨
      (commutF_pairLink (commutF_pairLink i).1).2.2 < (commutF_pairLink i).2.2 ∧
      let σ := commutF_generator (commutF_pairLink i).2.1
      let p := (commutF_pairLink i).1
      (σ (commutF_pairFirst p) = commutF_pairFirst i ∧
        σ (commutF_pairSecond p) = commutF_pairSecond i) ∨
      (σ (commutF_pairFirst p) = commutF_pairSecond i ∧
        σ (commutF_pairSecond p) = commutF_pairFirst i))
  else True

private theorem commutF_pairCheck0 :
    ∀ j : Fin 32, commutF_pairCheck (0 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck1 :
    ∀ j : Fin 32, commutF_pairCheck (1 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck2 :
    ∀ j : Fin 32, commutF_pairCheck (2 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck3 :
    ∀ j : Fin 32, commutF_pairCheck (3 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck4 :
    ∀ j : Fin 32, commutF_pairCheck (4 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck5 :
    ∀ j : Fin 32, commutF_pairCheck (5 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck6 :
    ∀ j : Fin 32, commutF_pairCheck (6 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck7 :
    ∀ j : Fin 32, commutF_pairCheck (7 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

private theorem commutF_pairCheck8 :
    ∀ j : Fin 32, commutF_pairCheck (8 * 32 + j.val) := by
  unfold commutF_pairCheck
  decide

theorem commutF_pairCheck_all (i : Fin 276) : commutF_pairCheck i.val := by
  have hb : i.val / 32 < 9 := by omega
  have hj : i.val % 32 < 32 := Nat.mod_lt _ (by decide)
  have hall : ∀ b : Fin 9, ∀ j : Fin 32, commutF_pairCheck (b.val * 32 + j.val) := by
    intro b
    fin_cases b
    · exact commutF_pairCheck0
    · exact commutF_pairCheck1
    · exact commutF_pairCheck2
    · exact commutF_pairCheck3
    · exact commutF_pairCheck4
    · exact commutF_pairCheck5
    · exact commutF_pairCheck6
    · exact commutF_pairCheck7
    · exact commutF_pairCheck8
  have he : i.val / 32 * 32 + i.val % 32 = i.val := by omega
  simpa only [he] using hall ⟨i.val / 32, hb⟩ ⟨i.val % 32, hj⟩

/-- Every pair in the table is strictly ordered. -/
theorem commutF_pair_ordered (i : Fin 276) : commutF_pairFirst i < commutF_pairSecond i := by
  have hc := commutF_pairCheck_all i
  simp only [commutF_pairCheck, dif_pos i.isLt] at hc
  exact hc.1

theorem commutF_pairMask_strictMono : StrictMono commutF_pairMask := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have hc := commutF_pairCheck_all i.castSucc
  simp only [commutF_pairCheck, dif_pos i.castSucc.isLt] at hc
  exact hc.2.1 (Nat.succ_lt_succ i.isLt)

/-- The pair spanning tree propagates symmetric predicates along the three generators. -/
theorem commutF_pair_tree (P : Fin 24 → Fin 24 → Prop) (h0 : P 0 4)
    (hs : ∀ i j, P i j → P j i)
    (hg : ∀ g : Fin 3, ∀ i j, P i j →
      P (commutF_generator g i) (commutF_generator g j))
    (i : Fin 276) : P (commutF_pairFirst i) (commutF_pairSecond i) := by
  have hall : ∀ n : ℕ, ∀ j : Fin 276, (commutF_pairLink j).2.2 = n →
      P (commutF_pairFirst j) (commutF_pairSecond j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      have hc := commutF_pairCheck_all j
      simp only [commutF_pairCheck, dif_pos j.isLt] at hc
      rcases hc.2.2 with hr | ⟨hp, he⟩
      · change j = 3 at hr
        rw [hr]
        exact h0
      · have ht := hg (commutF_pairLink j).2.1 _ _ (ih _ (hp.trans_eq hj) _ rfl)
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simpa only [h1, h2] using ht
        · exact hs _ _ (by simpa only [h1, h2] using ht)
  exact hall _ i rfl

/-- The pair table interpreted as ordered coordinate pairs. -/
def commutF_pairEnum (i : Fin 276) : LtPair :=
  ⟨(commutF_pairFirst i, commutF_pairSecond i), commutF_pair_ordered i⟩

/-- All 276 pairs occur in the certified tree. -/
theorem commutF_pairEnum_surjective : Function.Surjective commutF_pairEnum := by
  apply ((Fintype.bijective_iff_injective_and_card commutF_pairEnum).mpr ⟨?_, ?_⟩).2
  · intro i j he
    apply commutF_pairMask_strictMono.injective
    apply Fin.ext
    have h1 := congrArg (fun p : LtPair => p.val.1.val) he
    have h2 := congrArg (fun p : LtPair => p.val.2.val) he
    change (commutF_pairMask i).val / 24 = (commutF_pairMask j).val / 24 at h1
    change (commutF_pairMask i).val % 24 = (commutF_pairMask j).val % 24 at h2
    omega
  · rw [Fintype.card_fin, card_ltPair]

/-- Symmetric predicates propagated by the coordinate generators hold on every pair. -/
theorem commutF_pair_transitive (P : Fin 24 → Fin 24 → Prop) (h0 : P 0 4)
    (hs : ∀ i j, P i j → P j i)
    (hg : ∀ g : Fin 3, ∀ i j, P i j →
      P (commutF_generator g i) (commutF_generator g j)) (p : LtPair) :
    P p.val.1 p.val.2 := by
  obtain ⟨i, rfl⟩ := commutF_pairEnum_surjective p
  exact commutF_pair_tree P h0 hs hg i

/-- Every off-diagonal matrix unit has the common odd-line scalar. -/
theorem commutF_offdiag_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (i j : Fin 24) (hij : i ≠ j) :
    T (basisA s(i, j), 0, 0) =
      commutOddScalar T 0 0 • ((basisA s(i, j), 0, 0) : SpaceB) := by
  let P (i j : Fin 24) := T (basisA s(i, j), 0, 0) =
    commutOddScalar T 0 0 • ((basisA s(i, j), 0, 0) : SpaceB)
  have hs : ∀ i j, P i j → P j i := by
    intro i j he
    simpa only [P, Sym2.eq_swap] using he
  have hg (g : Fin 3) (i j : Fin 24) (he : P i j) :
      P (commutF_generator g i) (commutF_generator g j) :=
    commutF_pair_matrix_perm T h _ (commutF_generator_code g) i j _ he
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact commutF_pair_transitive P (commutF_pair_seed_matrix T h) hs hg ⟨(i, j), hlt⟩
  · exact hs j i (commutF_pair_transitive P (commutF_pair_seed_matrix T h) hs hg
      ⟨(j, i), hlt⟩)

/-- Both short lines of every pair have the common odd-line scalar. -/
theorem commutF_pair_short_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (p : LtPair) :
    T (0, Xlift (rMinus p.val.1 p.val.2), 0) =
      commutOddScalar T 0 0 • ((0, Xlift (rMinus p.val.1 p.val.2), 0) : SpaceB) ∧
    T (0, Xlift (rPlus p.val.1 p.val.2), 0) =
      commutOddScalar T 0 0 • ((0, Xlift (rPlus p.val.1 p.val.2), 0) : SpaceB) := by
  obtain ⟨a, hA, hm, hp⟩ := commutB_pair_lines T
    (fun r => h _ (commutRho_mem_Gmat r)) (h _ commutTau_mem_Gmat) p
  have he := hA.symm.trans (commutF_offdiag_scalar T h _ _ p.property.ne)
  have hc := congrArg (fun u : SpaceB => u.1.val p.val.1 p.val.2) he
  simp only [Prod.smul_fst, Submodule.coe_smul, Matrix.smul_apply, basisA_apply,
    ite_true, smul_eq_mul, mul_one] at hc
  exact ⟨by rw [hm, hc], by rw [hp, hc]⟩

/-- Every short-label line has the common odd-line scalar. -/
theorem commutF_short_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (l : ShortLabel) :
    T (0, Xlift (labelElt l), 0) =
      commutOddScalar T 0 0 • ((0, Xlift (labelElt l), 0) : SpaceB) := by
  rcases l with p | p | ⟨c, i⟩ | ⟨o, v⟩
  · exact (commutF_pair_short_scalar T h p).1
  · exact (commutF_pair_short_scalar T h p).2
  · exact (commutL_spin_odd_scalar T h).2 c i
  · simpa only [tbasis_oct] using commutF_octads_scalar T h o v

/-- The full short-coordinate space has the common odd-line scalar. -/
theorem commutF_X_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (x : SpaceX) :
    T (0, x, 0) = commutOddScalar T 0 0 • ((0, x, 0) : SpaceB) := by
  have hs (c : ShortIdx) : T (0, Pi.single c 1, 0) =
      commutOddScalar T 0 0 • ((0, Pi.single c 1, 0) : SpaceB) := by
    obtain ⟨l, rfl⟩ := labelIdx_surjective c
    simpa only [Xlift_labelElt] using commutF_short_scalar T h l
  have he : ((0, x, 0) : SpaceB) =
      ∑ c : ShortIdx, x c • ((0, Pi.single c 1, 0) : SpaceB) := by
    ext
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Prod.fst_sum, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [he, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [map_smul, hs, smul_comm]

/-- The residual after subtracting the common short-line scalar. -/
def commutF_residual (T : SpaceB →ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB :=
  T - commutOddScalar T 0 0 • LinearMap.id

/-- Subtracting a scalar endomorphism preserves commutation with the generated group. -/
theorem commutF_residual_commutes (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    ∀ g ∈ Generated.Gmat, ∀ u, commutF_residual T (g u) = g (commutF_residual T u) := by
  intro g hg u
  simp only [commutF_residual, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, h g hg, map_sub, map_smul]

/-- The residual vanishes on every off-diagonal matrix unit. -/
theorem commutF_residual_offdiag (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (i j : Fin 24) (hij : i ≠ j) : commutF_residual T (basisA s(i, j), 0, 0) = 0 := by
  simp only [commutF_residual, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, commutF_offdiag_scalar T h i j hij, sub_self]

/-- The residual sends every symmetric matrix to a diagonal matrix. -/
theorem commutF_residual_diagonal (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (A : symMat) (i j : Fin 24) (hij : i ≠ j) :
    (commutF_residual T (A, 0, 0)).1.val i j = 0 := by
  have hz (z : PairIdx) : (commutF_residual T (basisA z, 0, 0)).1.val i j = 0 := by
    induction z using Sym2.ind with
    | h k l =>
      by_cases hkl : k = l
      · subst l
        apply (commutB_Gmat_diagonal _ (commutF_residual_commutes T h) _ ?_).2 i j hij
        intro p q hpq
        simp only [coe_basisA, ite_true, Matrix.single_apply]
        split_ifs with he
        · exact (hpq (he.1.symm.trans he.2)).elim
        · rfl
      · rw [commutF_residual_offdiag T h k l hkl]
        rfl
  rw [commutB_A_sum, map_sum]
  simp only [map_smul, Prod.fst_sum, Prod.smul_fst, Submodule.coe_sum,
    Submodule.coe_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, hz,
    mul_zero, Finset.sum_const_zero]

theorem commutF_coord_eq : ∀ r s : Fin 4, ∀ c d : Fin 6,
    coord r c = coord s d ↔ r = s ∧ c = d := by decide

/-- The three column Hadamard correlations, written as sparse coefficient vectors. -/
theorem commutF_xi_correlation : ∀ c : Fin 6, ∀ r : Fin 3, ∀ k : Fin 24,
    4 * liftXiMatrix (coord 0 c) k * liftXiMatrix (coord r.succ c) k =
      ((Pi.single (coord 0 c) 1 : Fin 24 → ℚ) + Pi.single (coord r.succ c) 1 -
        ∑ s : Fin 3, if s = r then 0 else Pi.single (coord s.succ c) 1 :
          Fin 24 → ℚ) k := by
  intro c r k
  obtain ⟨⟨d, t⟩, rfl⟩ := liftXiCoords.surjective k
  change 4 * liftXiMatrix (coord 0 c) (coord t d) *
    liftXiMatrix (coord r.succ c) (coord t d) = _
  by_cases hc : c = d
  · subst d
    fin_cases r <;> fin_cases t <;>
      norm_num [liftXiMatrix, LinearMap.toMatrix'_apply, liftXiRat_coord, liftXiBlock,
        Fin.sum_univ_four, Fin.sum_univ_three, Pi.single_apply, commutF_coord_eq,
        liftXiCoords]
    all_goals simp only [ite_apply, Pi.zero_apply, Pi.single_apply, commutF_coord_eq,
      and_true]
    all_goals norm_num [Fin.ext_iff]
  · simp [liftXiMatrix, LinearMap.toMatrix'_apply, liftXiRat_coord, liftXiBlock,
      commutF_coord_eq, hc, Ne.symm hc, Fin.sum_univ_three, liftXiCoords, ite_apply]

/-- Diagonality of a Conway conjugate forces equality within each MOG column. -/
theorem commutF_xi_diagonal_columns (D : symMat)
    (hd : ∀ i j, i ≠ j → D.val i j = 0)
    (hx : ∀ i j, i ≠ j → (thetaA liftXiMatrixᵀ D).val i j = 0)
    (c : Fin 6) (r : Fin 4) : D.val (coord r c) (coord r c) = D.val (coord 0 c) (coord 0 c) := by
  have heD : D.val = Matrix.diagonal (fun k => D.val k k) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, hd i j hij]
  have hn : ∀ c : Fin 6, ∀ r : Fin 3, coord 0 c ≠ coord r.succ c := by decide
  have hh (s : Fin 3) :
      ∑ k, (4 * liftXiMatrix (coord 0 c) k * liftXiMatrix (coord s.succ c) k) *
        D.val k k = 0 := by
    have he := hx (coord 0 c) (coord s.succ c) (hn c s)
    change (liftXiMatrix * D.val * liftXiMatrixᵀ) (coord 0 c) (coord s.succ c) = 0 at he
    rw [heD] at he
    rw [Matrix.mul_apply] at he
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at he
    calc
      _ = 4 * ∑ k, liftXiMatrix (coord 0 c) k * D.val k k *
          liftXiMatrix (coord s.succ c) k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = 0 := by rw [he, mul_zero]
  simp_rw [commutF_xi_correlation] at hh
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  simp [Fin.sum_univ_three, Pi.single_apply, add_mul, sub_mul, ite_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at h0 h1 h2
  fin_cases r
  · rfl
  · change D.val (coord 1 c) (coord 1 c) = D.val (coord 0 c) (coord 0 c)
    linear_combination -(1 / 2 : ℚ) * h1 - (1 / 2 : ℚ) * h2
  · change D.val (coord 2 c) (coord 2 c) = D.val (coord 0 c) (coord 0 c)
    linear_combination -(1 / 2 : ℚ) * h0 - (1 / 2 : ℚ) * h2
  · change D.val (coord 3 c) (coord 3 c) = D.val (coord 0 c) (coord 0 c)
    linear_combination -(1 / 2 : ℚ) * h0 - (1 / 2 : ℚ) * h1

/-- Entries of a permutation congruence are reindexed by the inverse permutation. -/
theorem commutF_theta_perm_entry (σ : Equiv.Perm (Fin 24)) (A : symMat) (i j : Fin 24) :
    (thetaA (σ.permMatrix ℚ) A).val i j = A.val (σ.symm i) (σ.symm j) := by
  simp only [coe_thetaA, Matrix.transpose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply,
    id_eq, Equiv.Perm.inv_def]

/-- The residual image is constant within each MOG column. -/
theorem commutF_residual_columns (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (A : symMat)
    (i j : Fin 24) (hij : Code.col i = Code.col j) :
    (commutF_residual T (A, 0, 0)).1.val i i =
      (commutF_residual T (A, 0, 0)).1.val j j := by
  let D := (commutF_residual T (A, 0, 0)).1
  have hd := commutF_residual_diagonal T h A
  have hx : ∀ i j, i ≠ j → (thetaA liftXiMatrixᵀ D).val i j = 0 := by
    rw [← commutL_symMat_xi _ (commutF_residual_commutes T h) A]
    exact commutF_residual_diagonal T h _
  have hi := commutF_xi_diagonal_columns D hd hx (Code.col i) (Code.row i)
  have hj := commutF_xi_diagonal_columns D hd hx (Code.col j) (Code.row j)
  rw [coord_row_col] at hi hj
  exact hi.trans ((congrArg (fun c => D.val (coord 0 c) (coord 0 c)) hij).trans hj.symm)

/-- The transverse column partition forces every residual diagonal to be constant. -/
theorem commutF_residual_constant (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (A : symMat) (i : Fin 24) :
    (commutF_residual T (A, 0, 0)).1.val i i =
      (commutF_residual T (A, 0, 0)).1.val 0 0 := by
  apply commutF_transverse_constant _ (commutF_residual_columns T h A) _ i
  intro j k hjk
  have he := commutF_residual_columns T h (thetaA (commutF_transverse.permMatrix ℚ) A)
    j k hjk
  rw [commutL_symMat_perm _ (commutF_residual_commutes T h) _
    commutF_transverse_code A] at he
  have hi : commutF_transverse.symm = commutF_transverse := by decide
  simpa only [commutF_theta_perm_entry, hi] using he

/-- The identity symmetric matrix in the rational matrix block. -/
def commutF_identityMatrix : symMat := ⟨1, by simp [mem_symMat]⟩

/-- The distinguished identity vector in the rational Griess space. -/
def commutF_eOne : SpaceB := (commutF_identityMatrix, 0, 0)

/-- Projection onto the identity line: `u ↦ (bform u eOne / 24) • eOne`. -/
def commutF_P₀ : SpaceB →ₗ[ℚ] SpaceB :=
  ((1 / 24 : ℚ) • bform.flip commutF_eOne).smulRight commutF_eOne

theorem commutF_P₀_apply (u : SpaceB) :
    commutF_P₀ u = (bform u commutF_eOne / 24) • commutF_eOne := by
  change ((1 / 24 : ℚ) * bform u commutF_eOne) • commutF_eOne = _
  congr 1
  ring

theorem commutF_bform_identity (u : SpaceB) :
    bform u commutF_eOne = Matrix.trace u.1.val := by
  rw [bform_apply]
  simp [commutF_eOne, commutF_identityMatrix]

/-- The residual of every symmetric matrix lies on the identity line. -/
theorem commutF_residual_identity (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (A : symMat) :
    commutF_residual T (A, 0, 0) =
      (commutF_residual T (A, 0, 0)).1.val 0 0 • commutF_eOne := by
  have hs := commutF_residual_commutes T h
  have hp := commutPreservesA (commutF_residual T)
    (fun r => hs _ (commutRho_mem_Gmat r)) A
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    change (commutF_residual T (A, 0, 0)).1.val i j =
      (commutF_residual T (A, 0, 0)).1.val 0 0 * (1 : Matrix _ _ ℚ) i j
    by_cases hij : i = j
    · subst j
      simpa using commutF_residual_constant T h A i
    · simp [hij, commutF_residual_diagonal T h A i j hij]
  · have he := congrArg Prod.snd hp
    simpa [commutF_eOne] using he

/-- Coordinate permutations fix the identity matrix. -/
theorem commutF_theta_identity (σ : Equiv.Perm (Fin 24)) :
    thetaA (σ.permMatrix ℚ) commutF_identityMatrix = commutF_identityMatrix := by
  apply Subtype.ext
  ext i j
  rw [commutF_theta_perm_entry]
  change (1 : Matrix _ _ ℚ) (σ.symm i) (σ.symm j) = (1 : Matrix _ _ ℚ) i j
  simp only [Matrix.one_apply, σ.symm.injective.eq_iff]

/-- Coordinate permutations identify residual images of diagonal matrix units. -/
theorem commutF_residual_diag_perm (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) (i : Fin 24) :
    commutF_residual T (basisA s(σ i, σ i), 0, 0) =
      commutF_residual T (basisA s(i, i), 0, 0) := by
  have hs := commutF_residual_commutes T h
  obtain ⟨g, _, _, hg, hb⟩ := commutL_mathieu_blocks σ hσ
  have he := hs _ hg (basisA s(i, i), 0, 0)
  have hgA : ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) (basisA s(i, i), 0, 0) =
      (basisA s(σ i, σ i), 0, 0) := by
    rw [hb, commutF_basisA_perm]
    simp only [commutL_short_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hgI : ((g : AutO) : SpaceB ≃ₗ[ℚ] SpaceB) commutF_eOne = commutF_eOne := by
    rw [hb]
    change (thetaA (σ.permMatrix ℚ) commutF_identityMatrix,
      griessTrX (liftSignX _ _ (griessTrX 0)), _ * 0 * _) = commutF_eOne
    rw [commutF_theta_identity, commutL_short_zero, Matrix.mul_zero, Matrix.zero_mul]
    rfl
  rw [hgA] at he
  conv_rhs at he => rw [commutF_residual_identity T h, map_smul, hgI]
  exact he.trans (commutF_residual_identity T h _).symm

/-- Point transitivity identifies all residual diagonal matrix units. -/
theorem commutF_residual_diag_equal (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (i : Fin 24) :
    commutF_residual T (basisA s(i, i), 0, 0) =
      commutF_residual T (basisA s(0, 0), 0, 0) :=
  commutL_point_transitive (fun i => commutF_residual T (basisA s(i, i), 0, 0))
    (commutF_residual_diag_perm T h _ commutL_pointPermA_code)
    (commutF_residual_diag_perm T h _ commutL_pointPermB_code) i

/-- The residual on symmetric matrices is determined by the trace. -/
theorem commutF_residual_trace (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (A : symMat) :
    commutF_residual T (A, 0, 0) = Matrix.trace A.val •
      commutF_residual T (basisA s(0, 0), 0, 0) := by
  let inc : symMat →ₗ[ℚ] SpaceB := LinearMap.inl ℚ symMat (SpaceX × SpaceW)
  let tr : symMat →ₗ[ℚ] ℚ :=
    (Matrix.traceLinearMap (Fin 24) ℚ ℚ).comp symMat.subtype
  have he : (commutF_residual T).comp inc =
      tr.smulRight (commutF_residual T (basisA s(0, 0), 0, 0)) := by
    apply basisA.ext
    intro z
    change commutF_residual T (basisA z, 0, 0) =
      Matrix.trace (basisA z).val • commutF_residual T (basisA s(0, 0), 0, 0)
    induction z using Sym2.ind with
    | h i j =>
      by_cases hij : i = j
      · subst j
        rw [commutF_residual_diag_equal T h, coe_basisA, if_pos rfl,
          Matrix.trace_single_eq_same, one_smul]
      · rw [commutF_residual_offdiag T h i j hij, coe_basisA, if_neg hij,
          Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hij,
          Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hij), add_zero, zero_smul]
  exact LinearMap.congr_fun he A

/-- The commutant has the common short-line scalar on traceless symmetric matrices. -/
theorem commutF_traceless_scalar (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u))
    (A : symMat) (hA : Matrix.trace A.val = 0) :
    T (A, 0, 0) = commutOddScalar T 0 0 • ((A, 0, 0) : SpaceB) := by
  have he := commutF_residual_trace T h A
  rw [hA, zero_smul] at he
  exact sub_eq_zero.mp he

/-- On the full Griess space the residual depends only on the matrix trace. -/
theorem commutF_residual_full (T : SpaceB →ₗ[ℚ] SpaceB)
    (h : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) (u : SpaceB) :
    commutF_residual T u = Matrix.trace u.1.val •
      commutF_residual T (basisA s(0, 0), 0, 0) := by
  have hx : commutF_residual T (0, u.2.1, 0) = 0 := by
    simp only [commutF_residual, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, commutF_X_scalar T h, sub_self]
  have hw : commutF_residual T (0, 0, u.2.2) = 0 := by
    simp only [commutF_residual, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, (commutL_spin_odd_scalar T h).1, sub_self]
  have hu : u = ((u.1, 0, 0) : SpaceB) + (0, u.2.1, 0) + (0, 0, u.2.2) := by
    ext <;> simp
  conv_lhs => rw [hu, map_add, map_add, hx, hw, add_zero, add_zero]
  exact commutF_residual_trace T h u.1

/-- The rational commutant consists of a scalar identity and the identity-line projection. -/
theorem commutF_commutant_Gmat (T : SpaceB →ₗ[ℚ] SpaceB)
    (hT : ∀ g ∈ Generated.Gmat, ∀ u, T (g u) = g (T u)) :
    ∃ a b : ℚ, T = a • LinearMap.id + b • commutF_P₀ := by
  let c : ℚ := (commutF_residual T (basisA s(0, 0), 0, 0)).1.val 0 0
  refine ⟨commutOddScalar T 0 0, 24 * c, ?_⟩
  apply LinearMap.ext
  intro u
  have he := commutF_residual_full T hT u
  rw [commutF_residual_identity T hT] at he
  change T u - commutOddScalar T 0 0 • u =
    Matrix.trace u.1.val • (c • commutF_eOne) at he
  have hp : (24 * c) • commutF_P₀ u = Matrix.trace u.1.val • (c • commutF_eOne) := by
    rw [commutF_P₀_apply, commutF_bform_identity, smul_smul, smul_smul]
    congr 1
    ring
  change T u = commutOddScalar T 0 0 • u + (24 * c) • commutF_P₀ u
  rw [hp]
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

end VOA.Moonshine.ConwayNorton.M8
