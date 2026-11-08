import VOA.Moonshine.MoonshineCNGriessSign
import VOA.Moonshine.MoonshineLRLiftBlock

/-!
# Signed permutation action on the untwisted Griess dictionary

Every Leech isometry permutes the short pairs. The fixed dictionary phases turn the
comparison coboundary into rational signs.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.MonsterGriess.Code (classOf)
open VOA.LatGen VOA.IntegralLattice

/-- Equality up to sign is symmetric. -/
theorem liftSignPm_symm {a b : leech.carrier} (h : a = b ∨ a = -b) :
    b = a ∨ b = -a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

/-- Equality up to sign is transitive. -/
theorem liftSignPm_trans {a b c : leech.carrier}
    (h : a = b ∨ a = -b) (k : b = c ∨ b = -c) : a = c ∨ a = -c := by
  rcases h with rfl | rfl <;> rcases k with rfl | rfl <;> simp

/-- Every norm-four vector has a short representative. -/
theorem liftSignShort_exists (α : leech.carrier) (hα : leech.form α α = 4) :
    ∃ c : ShortIdx, α = shortVec c ∨ α = -shortVec c := by
  obtain ⟨p, hp⟩ := SpinLattice.phi0_bijective.2 (classOf (leechEquiv α : Fin 24 → ℤ))
  let c : ShortIdx := ⟨p, (isShortCoord_iff p).2 ⟨α, hα, hp.symm⟩⟩
  have hm := (leechEquiv_mem_minVecs_iff α).2 hα
  have hc : classOf (leechEquiv α : Fin 24 → ℤ) = classOf (uvec c) := by
    rw [classOf_uvec]
    exact hp.symm
  refine ⟨c, ?_⟩
  rcases (classOf_eq_iff hm (uvec_mem_minVecs c)).1 hc with h | h
  · exact Or.inl (eq_of_leechEquiv_coe (h.trans (leechEquiv_shortVec c).symm))
  · right
    apply eq_of_leechEquiv_coe
    rw [leechEquiv_coe_neg, leechEquiv_shortVec, h]

/-- The short representative of a norm-four vector is unique up to sign. -/
theorem liftSignShort_existsUnique (α : leech.carrier) (hα : leech.form α α = 4) :
    ∃! c : ShortIdx, α = shortVec c ∨ α = -shortVec c := by
  obtain ⟨c, hc⟩ := liftSignShort_exists α hα
  refine ⟨c, hc, fun d hd => ?_⟩
  exact shortSignDictionary_griessShortSign.pm_injective c d
    (liftSignPm_trans (liftSignPm_symm hd) hc)

section Isometry

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)

/-- The image short index, obtained from the image of its lattice representative. -/
def liftSignIndex (c : ShortIdx) : ShortIdx :=
  (liftSignShort_exists (ι (shortVec c)) ((hι _ _).trans (shortVec_norm c))).choose

theorem liftSignIndex_spec (c : ShortIdx) :
    ι (shortVec c) = shortVec (liftSignIndex ι hι c) ∨
      ι (shortVec c) = -shortVec (liftSignIndex ι hι c) :=
  (liftSignShort_exists (ι (shortVec c)) ((hι _ _).trans (shortVec_norm c))).choose_spec

theorem liftSignIndex_injective : Function.Injective (liftSignIndex ι hι) := by
  intro c d h
  have hc := liftSignIndex_spec ι hι c
  rw [h] at hc
  have he := liftSignPm_trans hc (liftSignPm_symm (liftSignIndex_spec ι hι d))
  apply shortSignDictionary_griessShortSign.pm_injective d c
  rcases he with he | he
  · exact Or.inl (isometry_injective leech leech ι leech_posDef hι he)
  · exact Or.inr (isometry_injective leech leech ι leech_posDef hι
      (he.trans (map_neg ι (shortVec d)).symm))

/-- The permutation of short pairs induced by a Leech isometry. -/
def liftSignPerm : Equiv.Perm ShortIdx :=
  Equiv.ofBijective (liftSignIndex ι hι)
    ⟨liftSignIndex_injective ι hι,
      Finite.surjective_of_injective (liftSignIndex_injective ι hι)⟩

theorem liftSignPerm_spec (c : ShortIdx) :
    ι (shortVec c) = shortVec (liftSignPerm ι hι c) ∨
      ι (shortVec c) = -shortVec (liftSignPerm ι hι c) :=
  liftSignIndex_spec ι hι c

/-- The comparison coboundary is one on doubles. -/
theorem liftSignLatCob_double (α : leech.carrier) :
    latCob leech leech ι (α + α) = 1 := by
  simpa only [zero_add, two_smul, latCob_zero] using
    (liftTwLatCob_add_two leech ι 0 α)

include hι in
/-- The diagonal cocycle identity determines the square of the coboundary. -/
theorem liftSignLatCob_sq (α : leech.carrier) :
    latCob leech leech ι α ^ 2 =
      latticeCocycle leech α α / latticeCocycle leech (ι α) (ι α) := by
  apply (eq_div_iff (latticeCocycle_ne_zero leech _ _)).2
  have h := latticeCocycle_map_mul_latCob leech leech leech_even leech_even ι hι α α
  rw [liftSignLatCob_double, mul_one] at h
  simpa only [pow_two, mul_comm] using h

/-- Simultaneously negating the arguments leaves the diagonal cocycle unchanged. -/
theorem liftSignCocycle_neg (α : leech.carrier) :
    latticeCocycle leech (-α) (-α) = latticeCocycle leech α α := by
  rw [latticeCocycle_neg_left, latticeCocycle_neg_right]

/-- The fixed short phases are nonzero. -/
theorem liftSignPhase_ne_zero (c : ShortIdx) : griessShortSign c ≠ 0 := by
  intro h
  have hs := griessShortSign_sq c
  rw [h, zero_pow (by decide), zero_mul] at hs
  exact zero_ne_one hs

/-- The exact complex ratio before it is identified with a rational sign. -/
def liftSignRatio (c : ShortIdx) : ℂ :=
  griessShortSign c * latCob leech leech ι (shortVec c) /
    griessShortSign (liftSignPerm ι hι c)

theorem liftSignRatio_sq (c : ShortIdx) : liftSignRatio ι hι c ^ 2 = 1 := by
  have he : latticeCocycle leech (ι (shortVec c)) (ι (shortVec c)) =
      latticeCocycle leech (shortVec (liftSignPerm ι hι c))
        (shortVec (liftSignPerm ι hι c)) := by
    rcases liftSignPerm_spec ι hι c with h | h
    · rw [h]
    · rw [h, liftSignCocycle_neg]
  have hc := griessShortSign_sq c
  have hd := griessShortSign_sq (liftSignPerm ι hι c)
  rw [liftSignRatio, div_pow, mul_pow, liftSignLatCob_sq ι hι, he]
  apply (div_eq_one_iff_eq (pow_ne_zero 2 (liftSignPhase_ne_zero _))).2
  have hd' := (eq_div_iff (latticeCocycle_ne_zero leech
    (shortVec (liftSignPerm ι hι c)) (shortVec (liftSignPerm ι hι c)))).2 hd
  rw [hd']
  rw [← mul_div_assoc, hc]

/-- Every phase ratio is a sign. -/
theorem liftSignRatio_eq_one_or_neg_one (c : ShortIdx) :
    liftSignRatio ι hι c = 1 ∨ liftSignRatio ι hι c = -1 :=
  (sq_eq_one_iff).1 (liftSignRatio_sq ι hι c)

/-- Rational weights of the signed permutation. -/
def liftSignWeight (c : ShortIdx) : ℚ :=
  if liftSignRatio ι hι c = 1 then 1 else -1

theorem liftSignWeight_cast (c : ShortIdx) :
    (liftSignWeight ι hι c : ℂ) = liftSignRatio ι hι c := by
  rcases liftSignRatio_eq_one_or_neg_one ι hι c with h | h
  · simp [liftSignWeight, h]
  · norm_num [liftSignWeight, h]

theorem liftSignWeight_sign (c : ShortIdx) :
    liftSignWeight ι hι c = 1 ∨ liftSignWeight ι hι c = -1 := by
  unfold liftSignWeight
  split_ifs <;> simp

theorem liftSignWeight_phase (c : ShortIdx) :
    (liftSignWeight ι hι c : ℂ) * griessShortSign (liftSignPerm ι hι c) =
      griessShortSign c * latCob leech leech ι (shortVec c) := by
  rw [liftSignWeight_cast, liftSignRatio,
    div_mul_cancel₀ _ (liftSignPhase_ne_zero _)]

/-- The signed permutation on the rational short coordinates. -/
def liftSignX (x : SpaceX) : SpaceX :=
  liftBlockShortX (liftSignPerm ι hι) (liftSignWeight ι hι) x

theorem liftSignX_apply (x : SpaceX) (c : ShortIdx) :
    liftSignX ι hι x (liftSignPerm ι hι c) = liftSignWeight ι hι c * x c := by
  simp only [liftSignX, liftBlockShortX, Equiv.symm_apply_apply]

variable (hsurj : Function.Surjective ι)

/-- The short block of the lifted automorphism is a rational signed permutation. -/
theorem liftSignNat_shortBlock (x : SpaceX) :
    liftTwVnatAut ι hι hsurj
        (untwistedDictNat griessShortSign (shortBlock x) : Vnat) =
      (untwistedDictNat griessShortSign (shortBlock (liftSignX ι hι x)) : Vnat) :=
  liftBlockNat_shortBlock_reindex ι hι hsurj griessShortSign x
    (liftSignPerm ι hι) (liftSignPerm_spec ι hι)
    (liftSignWeight ι hι) (liftSignWeight_phase ι hι)

/-- The full untwisted block: rational matrix congruence and signed short permutation. -/
theorem liftSignNat_untwisted (A : symMat) (x : SpaceX) :
    liftTwVnatAut ι hι hsurj
        (untwistedDictNat griessShortSign (A, x, 0) : Vnat) =
      (untwistedDictNat griessShortSign
        (liftBlockSymMat ι A, liftSignX ι hι x, 0) : Vnat) := by
  change liftTwVnatAut ι hι hsurj
    ((matDict A + shortDict griessShortSign x, 0) : Vnat) =
      ((matDict (liftBlockSymMat ι A) +
        shortDict griessShortSign (liftSignX ι hι x), 0) : Vnat)
  simp only [liftTwVnatAut_apply, map_add, map_zero, liftBlockPlus_matDict,
    liftBlockPlus_shortDict_reindex ι hι hsurj griessShortSign x
      (liftSignPerm ι hι) (liftSignPerm_spec ι hι)
      (liftSignWeight ι hι) (liftSignWeight_phase ι hι)]
  rfl

/-- The full block formula for any input whose twisted coordinate vanishes. -/
theorem liftSignNat_of_zeroW (u : SpaceB) (hu : u.2.2 = 0) :
    liftTwVnatAut ι hι hsurj (untwistedDictNat griessShortSign u : Vnat) =
      (untwistedDictNat griessShortSign
        (liftBlockSymMat ι u.1, liftSignX ι hι u.2.1, 0) : Vnat) := by
  have he : u = (u.1, u.2.1, 0) := by
    rw [← hu]
  conv_lhs => rw [he]
  exact liftSignNat_untwisted ι hι hsurj u.1 u.2.1

end Isometry

end VOA.Moonshine.ConwayNorton.M8
