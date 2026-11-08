import VOA.Moonshine.MoonshineLRLiftLiftable3

/-!
# Golay and Mathieu lifts lie in the rational Monster

The frame sublattice consists of vectors whose Conway coordinates have a common even
residue modulo four and whose coordinate sum is divisible by eight. Its spin operators
are diagonal: they commute with a separating family of diagonal cocode and frame operators.
Golay sign changes and all code-preserving coordinate permutations preserve this sublattice.

The normalized charge operator therefore normalizes a separating diagonal family. Each row
has exactly one nonzero entry, and orthogonality makes that entry a sign. This constructs
`liftSpinGolayPerm` / `liftSpinGolaySigns` and `liftSpinMathieuPerm` / `liftSpinMathieuSigns`
noncomputably from the existing charge action; no enumeration of the spin module is used.
Their row and sign identities hold for every lattice vector. Specializing to the canonical
basis discharges `liftGenOfSignedBasis` for both families, with the existing chosen VOA lift.

The construction supplies signed permutations by unique row support, rather than closed
bit-coordinate formulas. It does not treat the nonmonomial Conway generator `ξ`.
-/

noncomputable section

namespace VOA.Moonshine.ConwayNorton.M8

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen
open VOA.Moonshine.AutMonster VOA.Moonshine.GriessDictionary
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterAction
open VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.LeechMatch
open VOA.Moonshine.MonsterGriess.SpinLattice
open VOA.Moonshine.FrameT
open scoped Matrix

/-- The normalized charge operator, with exactly the normalization of the chosen lift. -/
def liftSpinCharge (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β) :
    SpinRep ≃ₗ[ℂ] SpinRep :=
  (liftWSpinCharge ι hι).trans (LinearEquiv.smulOfUnit (liftWScalar ι hι))

theorem liftSpinCharge_apply (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β) (s : SpinRep) :
    liftSpinCharge ι hι s = (liftWScalar ι hι : ℂ) • liftWSpinCharge ι hι s := rfl

/-- The unphased charge intertwining identity for the actual normalized charge operator. -/
theorem liftSpinCharge_intertwine (ι : leech.carrier →ₗ[ℤ] leech.carrier)
    (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
    (α : leech.carrier) (s : SpinRep) :
    liftSpinCharge ι hι (liftMonoQmat α |>.map (Rat.castHom ℂ) |>.mulVec s) =
      (liftMonoWeight ι α : ℂ) •
        ((liftMonoQmat (ι α)).map (Rat.castHom ℂ) *ᵥ liftSpinCharge ι hι s) := by
  have h := liftLiftableChargeIntertwine ι hι α s
  rw [spinOp, spinOp, Matrix.smul_mulVec, Matrix.smul_mulVec] at h
  change (liftWSpinCharge ι hι)
      (signRefinement (coordOfRed (red leech α)) • (_ *ᵥ s) : SpinRep) = _ at h
  erw [LinearEquiv.map_smul] at h
  rw [smul_smul, ← liftMonoWeight_phase ι hι, mul_comm,
    ← smul_smul] at h
  have h' := (smul_right_injective _ (liftMonoRefinement_ne_zero α)) h
  simp only [liftSpinCharge_apply, liftMonoQmat_map, h']
  funext i
  change (liftWScalar ι hι : ℂ) * ((liftMonoWeight ι α : ℂ) * ∑ j, _ * _) =
    (liftMonoWeight ι α : ℂ) * ∑ j, _ * ((liftWScalar ι hι : ℂ) * _)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- An orthogonal linear map normalizing a separating family of diagonal operators is
a signed permutation, and consequently is defined over the rationals. -/
theorem liftSpinRational_of_diagonal {T : Type*} (E : (SpinIdx → ℂ) ≃ₗ[ℂ] (SpinIdx → ℂ))
    (horth : ∀ v w, E v ⬝ᵥ E w = v ⬝ᵥ w)
    (d e : T → SpinIdx → ℂ)
    (hint : ∀ t v, E (Matrix.diagonal (d t) *ᵥ v) =
      Matrix.diagonal (e t) *ᵥ E v)
    (hsep : ∀ j k, (∀ t, d t j = d t k) → j = k) :
    ∃ (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2),
      ∀ v, E v = (liftGenSignedMatrix σ ε).map (Rat.castHom ℂ) *ᵥ v := by
  classical
  let M : Matrix SpinIdx SpinIdx ℂ := fun i j => E (Pi.single j 1) i
  have hMv (v : SpinIdx → ℂ) : E v = M *ᵥ v := by
    conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
    ext i
    simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, M]
    apply Finset.sum_congr rfl
    intro j _
    have h : Pi.single j (v j) = v j • Pi.single j (1 : ℂ) := by
      ext k
      by_cases hk : k = j
      · subst k; simp
      · simp [hk]
    rw [h, map_smul]
    simp [mul_comm]
  have hentry (t : T) (i j : SpinIdx) : M i j * d t j = e t i * M i j := by
    have h := congrFun (hint t (Pi.single j 1)) i
    have hd : Matrix.diagonal (d t) *ᵥ Pi.single j 1 = d t j • Pi.single j 1 := by
      ext k
      simp [Matrix.mulVec_diagonal, Pi.single_apply, Pi.smul_apply]
      split_ifs <;> simp_all
    rw [hd, map_smul, Matrix.mulVec_diagonal] at h
    simpa only [Pi.smul_apply, smul_eq_mul, M, mul_comm] using h
  have hunique (i j k : SpinIdx) (hj : M i j ≠ 0) (hk : M i k ≠ 0) : j = k := by
    apply hsep j k
    intro t
    have h (l : SpinIdx) (hl : M i l ≠ 0) : d t l = e t i := by
      apply mul_left_cancel₀ hl
      rw [hentry, mul_comm]
    exact (h j hj).trans (h k hk).symm
  have hrow (i : SpinIdx) : ∃ j, M i j ≠ 0 := by
    by_contra! h
    obtain ⟨v, hv⟩ := E.surjective (Pi.single i 1)
    have hi := congrFun hv i
    rw [hMv] at hi
    simp [Matrix.mulVec, dotProduct, h] at hi
  choose f hf using hrow
  have hzero (i j : SpinIdx) (h : j ≠ f i) : M i j = 0 := by
    by_contra hn
    exact h (hunique i j (f i) hn (hf i))
  have hsurj : Function.Surjective f := by
    intro j
    by_contra! hj
    have hz : E (Pi.single j 1) = 0 := funext fun i => hzero i j (Ne.symm (hj i))
    have he := E.injective (hz.trans E.map_zero.symm)
    have := congrFun he j
    simp at this
  let σ : Equiv.Perm SpinIdx := Equiv.ofBijective f
    ⟨(Finite.injective_iff_surjective).mpr hsurj, hsurj⟩
  have hsquare (i : SpinIdx) : M i (f i) * M i (f i) = 1 := by
    have h := horth (Pi.single (f i) 1) (Pi.single (f i) 1)
    change (∑ k, M k (f i) * M k (f i)) = _ at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro k _ hki
      rw [hzero k (f i) (fun he => hki (σ.injective he.symm))]
      simp
    · simp
  let ε : SpinIdx → ZMod 2 := fun i => if M i (f i) = 1 then 0 else 1
  have heps (i : SpinIdx) : sgnR ℂ (ε i) = M i (f i) := by
    rcases mul_self_eq_one_iff.mp (hsquare i) with h | h
    · simp [ε, h]
    · norm_num [ε, h]
  refine ⟨σ, ε, fun v => (hMv v).trans ?_⟩
  congr 1
  ext i j
  simp only [liftGenSignedMatrix, map_spm, spm_apply]
  change M i j = if j = f i then sgnR ℂ (ε i) else 0
  split_ifs with h
  · rw [h, heps]
  · exact hzero i j h

/-- Lattice representatives of the cocode half of the spin coordinates. -/
def liftSpinLambda (x : Fin 24 → ZMod 2) : leech.carrier :=
  leechEquiv.symm ⟨lamSum x, lamSum_mem x⟩

theorem liftSpinLambda_coordinates (x : Fin 24 → ZMod 2) :
    (leechEquiv (liftSpinLambda x) : Fin 24 → ℤ) = lamSum x := by
  exact congrArg Subtype.val (leechEquiv.apply_symm_apply _)

theorem liftSpinLambda_coord (x : Fin 24 → ZMod 2) :
    coordOfRed (red leech (liftSpinLambda x)) = (0, Submodule.Quotient.mk x) := by
  apply phi0_injective
  rw [phi0_coordOfRed_red, phi0_apply,
    show lamT 0 = 0 from lamTHom.map_zero, zero_add, lamCocode_mk]
  unfold liftSpinLambda lamVec cls
  rw [leechEquiv.apply_symm_apply]

/-- The even cocode operators are diagonal in the existing spin basis. -/
theorem liftSpinLambda_diagonal (x : Fin 24 → ZMod 2)
    (hx : pair ΩC (Submodule.Quotient.mk x) = 0) :
    (liftMonoQmat (liftSpinLambda x)).map (Rat.castHom ℂ) =
      Matrix.diagonal (fun i : SpinIdx => sgnR ℂ (pair i.2 (Submodule.Quotient.mk x))) := by
  rw [liftMonoQmat_map, liftSpinLambda_coord]
  ext i j
  simp only [qmatR_apply, qPerm, hx, add_zero, shift_zero, qSign, map_zero,
    mul_zero, zero_add, Prod.mk.eta, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

/-- A separating family: the frame involution and all even cocode classes. -/
def liftSpinTest := Unit ⊕ {x : Fin 24 → ZMod 2 // pair ΩC (Submodule.Quotient.mk x) = 0}

def liftSpinTestVector : liftSpinTest → leech.carrier
  | .inl _ => frameW
  | .inr x => liftSpinLambda x.val

def liftSpinTestValue : liftSpinTest → SpinIdx → ℂ
  | .inl _, i => sgnR ℂ i.1
  | .inr x, i => sgnR ℂ (pair i.2 (Submodule.Quotient.mk x.val))

theorem liftSpinTest_diagonal (t : liftSpinTest) :
    (liftMonoQmat (liftSpinTestVector t)).map (Rat.castHom ℂ) =
      Matrix.diagonal (liftSpinTestValue t) := by
  cases t with
  | inl u =>
    exact (liftMonoQmat_map frameW).trans
      (by rw [coordOfRed_red_frameW]; exact qmatR_ΩC_thetaD)
  | inr x => exact liftSpinLambda_diagonal x.val x.property

theorem liftSpinSgn_injective : Function.Injective (sgnR ℂ) := by
  intro a b h
  rw [sgnR_eq_sgn, sgnR_eq_sgn] at h
  exact sgn_injective h

/-- The diagonal tests distinguish all 4096 spin rows. -/
theorem liftSpinTest_separates (i j : SpinIdx)
    (h : ∀ t, liftSpinTestValue t i = liftSpinTestValue t j) : i = j := by
  apply Prod.ext
  · exact liftSpinSgn_injective (h (.inl ()))
  · have heven (δ : Cocode) (hδ : pair ΩC δ = 0) : pair i.2 δ = pair j.2 δ := by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ δ
      exact liftSpinSgn_injective (h (.inr ⟨x, hδ⟩))
    obtain ⟨δ₀, hδ₀⟩ := exists_pair_eq μ₀
    have hall (δ : Cocode) : pair i.2 δ = pair j.2 δ := by
      have hp : pair ΩC (δ + pair ΩC δ • δ₀) = 0 := by
        rw [map_add, map_smul, hδ₀, μ₀_ΩC, smul_eq_mul, mul_one, zmod2_add_self]
      have hh := heven (δ + pair ΩC δ • δ₀) hp
      simpa only [map_add, map_smul, hδ₀, μ₀_coe, smul_zero, add_zero] using hh
    apply Subtype.ext
    apply Subtype.ext
    funext k
    have hh := hall (Submodule.Quotient.mk (Pi.single k 1))
    simpa only [pair_mk, dotProduct_single, mul_one] using hh

/-- The frame sublattice: coordinates have one even residue modulo four, and sum zero
modulo eight. This description is preserved by the monomial lattice generators. -/
def liftSpinFrameLattice (α : leech.carrier) : Prop :=
  (∃ (n : ℤ) (k : Fin 24 → ℤ),
    ∀ i, (leechEquiv α : Fin 24 → ℤ) i = 2 * n + 4 * k i) ∧
    8 ∣ ∑ i, (leechEquiv α : Fin 24 → ℤ) i

theorem liftSpinEvenWeight (x : Fin 24 → ZMod 2)
    (hx : pair ΩC (Submodule.Quotient.mk x) = 0) :
    2 ∣ (hammingNorm x : ℤ) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
  rw [← MonsterGriess.Code.sum_bitLift]
  simp only [Int.cast_sum, MonsterGriess.Code.bitLift_cast]
  simpa only [pair_mk, coe_ΩC, MonsterGriess.Code.Ω, dotProduct, one_mul] using hx

theorem liftSpinFrameW_mem : liftSpinFrameLattice frameW := by
  constructor
  · refine ⟨0, fun i => 2 * (Pi.single 0 (1 : ℤ) : Fin 24 → ℤ) i, fun i => ?_⟩
    rw [leechEquiv_frameW]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [leechEquiv_frameW]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact dvd_mul_right 8 _

theorem liftSpinLambda_mem (x : Fin 24 → ZMod 2)
    (hx : pair ΩC (Submodule.Quotient.mk x) = 0) :
    liftSpinFrameLattice (liftSpinLambda x) := by
  obtain ⟨n, hn⟩ := liftSpinEvenWeight x hx
  constructor
  · refine ⟨n, fun i => -bitLift (x i), fun i => ?_⟩
    rw [liftSpinLambda_coordinates, lamSum, hn]
    ring
  · rw [liftSpinLambda_coordinates]
    have hsum : (∑ i, lamSum x i) = 20 * (hammingNorm x : ℤ) := by
      simp only [lamSum, Finset.sum_sub_distrib, ← Finset.mul_sum,
        MonsterGriess.Code.sum_bitLift, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsum, hn]
    exact ⟨5 * n, by ring⟩

theorem liftSpinTest_mem (t : liftSpinTest) : liftSpinFrameLattice (liftSpinTestVector t) := by
  cases t with
  | inl _ => exact liftSpinFrameW_mem
  | inr x => exact liftSpinLambda_mem x.val x.property

/-- Every vector in the frame sublattice pairs evenly with all diagonal spin tests. -/
theorem liftSpinFrame_pair_even {α : leech.carrier} (hα : liftSpinFrameLattice α)
    (t : liftSpinTest) : Even (leech.form α (liftSpinTestVector t)) := by
  obtain ⟨⟨n, k, hk⟩, a, ha⟩ := hα
  cases t with
  | inl _ =>
    have hf := leechEquiv_dotProduct α frameW
    rw [leechEquiv_frameW, dotProduct_smul, dotProduct_single, mul_one] at hf
    change 8 * (leechEquiv α : Fin 24 → ℤ) 0 = 8 * leech.form α frameW at hf
    have he : leech.form α frameW = 2 * n + 4 * k 0 := by
      have := hk 0
      omega
    exact ⟨n + 2 * k 0, by change leech.form α frameW = _; omega⟩
  | inr x =>
    obtain ⟨b, hb⟩ := liftSpinEvenWeight x.val x.property
    have hf := leechEquiv_dotProduct α (liftSpinLambda x.val)
    rw [liftSpinLambda_coordinates] at hf
    have hd : (leechEquiv α : Fin 24 → ℤ) ⬝ᵥ lamSum x.val =
        (hammingNorm x.val : ℤ) * (∑ i, (leechEquiv α : Fin 24 → ℤ) i) -
          4 * (2 * n * (hammingNorm x.val : ℤ) +
            4 * ∑ i, k i * bitLift (x.val i)) := by
      simp only [dotProduct, lamSum, mul_sub, Finset.sum_sub_distrib]
      rw [show (∑ i, (leechEquiv α : Fin 24 → ℤ) i * (hammingNorm x.val : ℤ)) =
        (hammingNorm x.val : ℤ) * ∑ i, (leechEquiv α : Fin 24 → ℤ) i by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
      congr 1
      rw [← MonsterGriess.Code.sum_bitLift]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hk]
      ring
    rw [hd, hb, ha] at hf
    refine ⟨b * a - n * b - ∑ i, k i * bitLift (x.val i), ?_⟩
    change leech.form α (liftSpinLambda x.val) = _
    nlinarith

/-- Even lattice pairing implies commutation of the unphased spin matrices. -/
theorem liftSpinQmat_commute (α β : leech.carrier) (h : Even (leech.form α β)) :
    (liftMonoQmat α).map (Rat.castHom ℂ) * (liftMonoQmat β).map (Rat.castHom ℂ) =
      (liftMonoQmat β).map (Rat.castHom ℂ) * (liftMonoQmat α).map (Rat.castHom ℂ) := by
  have hs : spinOp (coordOfRed (red leech α)) * spinOp (coordOfRed (red leech β)) =
      spinOp (coordOfRed (red leech β)) * spinOp (coordOfRed (red leech α)) := by
    rw [spinOp_red_mul, spinOp_red_mul, latticeCocycle_swap_sign leech leech_even α β,
      h.neg_one_zpow, one_mul, add_comm α β]
  rw [spinOp, spinOp, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm] at hs
  rw [liftMonoQmat_map, liftMonoQmat_map]
  exact (smul_right_injective _
    (mul_ne_zero (liftMonoRefinement_ne_zero β) (liftMonoRefinement_ne_zero α))) hs

/-- The spin matrix of every frame-sublattice vector is diagonal. -/
theorem liftSpinFrame_diagonal {α : leech.carrier} (hα : liftSpinFrameLattice α) :
    ∃ d : SpinIdx → ℂ, (liftMonoQmat α).map (Rat.castHom ℂ) = Matrix.diagonal d := by
  let A := (liftMonoQmat α).map (Rat.castHom ℂ)
  refine ⟨fun i => A i i, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j; simp [A]
  · rw [Matrix.diagonal_apply_ne _ hij]
    by_contra hn
    apply hij
    apply liftSpinTest_separates i j
    intro t
    have h := liftSpinQmat_commute α (liftSpinTestVector t) (liftSpinFrame_pair_even hα t)
    rw [liftSpinTest_diagonal] at h
    have hh := congrArg (fun M : Matrix SpinIdx SpinIdx ℂ => M i j) h
    change (A * Matrix.diagonal (liftSpinTestValue t)) i j =
      (Matrix.diagonal (liftSpinTestValue t) * A) i j at hh
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
    exact mul_right_cancel₀ hn ((mul_comm _ _).trans hh).symm

/-- Golay coordinate sign changes preserve the frame sublattice. -/
theorem liftSpinGolay_frame (c : MonsterGriess.Code.C) {α : leech.carrier}
    (hα : liftSpinFrameLattice α) : liftSpinFrameLattice (liftGenGolay c α) := by
  obtain ⟨⟨n, k, hk⟩, a, ha⟩ := hα
  constructor
  · refine ⟨n, fun i => if c.val i = 0 then k i else -n - k i, fun i => ?_⟩
    rw [liftGenGolay_coordinates]
    simp only [liftGenSign]
    split_ifs
    · exact hk i
    · rw [hk]
      ring
  · obtain ⟨b, hb⟩ := liftGenSign_support_sum c (leechEquiv α).property
    simp only [liftGenGolay_coordinates, liftGenSign_formula, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum, hb, ha]
    exact ⟨a - b, by ring⟩

/-- Every code-preserving coordinate permutation preserves the frame sublattice. -/
theorem liftSpinMathieu_frame (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ)
    {α : leech.carrier} (hα : liftSpinFrameLattice α) :
    liftSpinFrameLattice (liftGenMathieu σ hσ α) := by
  obtain ⟨⟨n, k, hk⟩, ha⟩ := hα
  constructor
  · exact ⟨n, fun i => k (σ.symm i), fun i => by
      rw [liftGenMathieu_coordinates, permLin_apply]; exact hk _⟩
  · rwa [liftGenMathieu_coordinates, sum_permLin]

/-- Equality of nonzero signed permutation rows determines both the column and its sign. -/
theorem liftSpinSpm_rows (f g : SpinIdx → SpinIdx) (a b : SpinIdx → ZMod 2) (w : ℚ)
    (h : spm ℚ f a = w • spm ℚ g b) (i : SpinIdx) :
    f i = g i ∧ sgnR ℚ (a i) = w * sgnR ℚ (b i) := by
  have hi := congrArg (fun M : Matrix SpinIdx SpinIdx ℚ => M i (f i)) h
  simp only [spm_apply, Matrix.smul_apply, smul_eq_mul, if_true] at hi
  have hp : f i = g i := by
    by_contra hn
    rw [if_neg hn, mul_zero] at hi
    have hs := sgnR_mul_self (R := ℚ) (a i)
    rw [hi, zero_mul] at hs
    exact zero_ne_one hs
  exact ⟨hp, by simpa only [if_pos hp] using hi⟩

section FramePreserving

variable (ι : leech.carrier →ₗ[ℤ] leech.carrier)
  (hι : ∀ α β, leech.form (ι α) (ι β) = leech.form α β)
  (hframe : ∀ α, liftSpinFrameLattice α → liftSpinFrameLattice (ι α))

include hframe in
/-- A frame-preserving lattice isometry has a signed permutation charge action, with
the signs of the chosen VOA normalization already included. -/
theorem liftSpinSigned_exists :
    ∃ (σ : Equiv.Perm SpinIdx) (ε : SpinIdx → ZMod 2),
      ∀ v : SpinRep, liftSpinCharge ι hι v =
        (liftGenSignedMatrix σ ε).map (Rat.castHom ℂ) *ᵥ v := by
  classical
  choose d hd using fun t =>
    liftSpinFrame_diagonal (hframe (liftSpinTestVector t) (liftSpinTest_mem t))
  let E : (SpinIdx → ℂ) ≃ₗ[ℂ] (SpinIdx → ℂ) := liftSpinCharge ι hι
  apply liftSpinRational_of_diagonal E (liftLiftableChargeDot ι hι) liftSpinTestValue
    (fun t i => (liftMonoWeight ι (liftSpinTestVector t) : ℂ) * d t i) _
    liftSpinTest_separates
  intro t v
  have h := liftSpinCharge_intertwine ι hι (liftSpinTestVector t) v
  rw [liftSpinTest_diagonal, hd] at h
  refine h.trans ?_
  change (liftMonoWeight ι (liftSpinTestVector t) : ℂ) •
    (Matrix.diagonal (d t) *ᵥ E v) = _
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal]
  exact (mul_assoc _ _ _).symm

/-- The induced spin permutation, characterized by the unique nonzero entry in each row
of the normalized charge operator. -/
def liftSpinPerm : Equiv.Perm SpinIdx := (liftSpinSigned_exists ι hι hframe).choose

/-- The signs accompanying the induced spin permutation. -/
def liftSpinSigns : SpinIdx → ZMod 2 := (liftSpinSigned_exists ι hι hframe).choose_spec.choose

theorem liftSpinSigned_spec (v : SpinRep) :
    liftSpinCharge ι hι v =
      (liftGenSignedMatrix (liftSpinPerm ι hι hframe) (liftSpinSigns ι hι hframe)).map
        (Rat.castHom ℂ) *ᵥ v :=
  (liftSpinSigned_exists ι hι hframe).choose_spec.choose_spec v

/-- The induced rational signed permutation satisfies the complete intertwining identity. -/
theorem liftSpinSigned_intertwine (α : leech.carrier) :
    liftGenSignedMatrix (liftSpinPerm ι hι hframe) (liftSpinSigns ι hι hframe) *
      liftMonoQmat α = liftMonoWeight ι α •
        (liftMonoQmat (ι α) *
          liftGenSignedMatrix (liftSpinPerm ι hι hframe) (liftSpinSigns ι hι hframe)) := by
  let R := liftGenSignedMatrix (liftSpinPerm ι hι hframe) (liftSpinSigns ι hι hframe)
  have hmap (w : ℚ) (M : Matrix SpinIdx SpinIdx ℚ) :
      (w • M).map (Rat.castHom ℂ) = (w : ℂ) • M.map (Rat.castHom ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Rat.coe_castHom, smul_eq_mul,
      Rat.cast_mul]
  suffices h : (R * liftMonoQmat α).map (Rat.castHom ℂ) =
      (liftMonoWeight ι α • (liftMonoQmat (ι α) * R)).map (Rat.castHom ℂ) from
    Matrix.map_injective (Rat.cast_injective (α := ℂ)) h
  rw [Matrix.map_mul (f := Rat.castHom ℂ), hmap, Matrix.map_mul (f := Rat.castHom ℂ)]
  ext i j
  have h := liftSpinCharge_intertwine ι hι α (Pi.single j 1)
  rw [liftSpinSigned_spec ι hι hframe, liftSpinSigned_spec ι hι hframe] at h
  have hi := congrFun h i
  change (R.map (Rat.castHom ℂ) *ᵥ
      ((liftMonoQmat α).map (Rat.castHom ℂ) *ᵥ Pi.single j 1)) i =
    (liftMonoWeight ι α : ℂ) *
      ((liftMonoQmat (ι α)).map (Rat.castHom ℂ) *ᵥ
        (R.map (Rat.castHom ℂ) *ᵥ Pi.single j 1)) i at hi
  simp only [Matrix.mulVec_single_one] at hi
  exact hi

/-- The row-permutation and sign identities hold on every lattice vector, hence on the
24 basis vectors required by the preceding file. -/
theorem liftSpinSigned_rows (α : leech.carrier) (i : SpinIdx) :
    let σ := liftSpinPerm ι hι hframe
    let ε := liftSpinSigns ι hι hframe
    let p := coordOfRed (red leech α)
    let q := coordOfRed (red leech (ι α))
    qPerm p.1 p.2 (σ i) = σ (qPerm q.1 q.2 i) ∧
      sgnR ℚ (ε i + qSign 0 p.1 p.2 (σ i)) =
        liftMonoWeight ι α * sgnR ℚ (qSign 0 q.1 q.2 i + ε (qPerm q.1 q.2 i)) := by
  have h := liftSpinSigned_intertwine ι hι hframe α
  unfold liftGenSignedMatrix liftMonoQmat qmatR at h
  rw [spm_mul_spm, spm_mul_spm] at h
  exact liftSpinSpm_rows _ _ _ _ _ h i

include hframe in
/-- Every frame-preserving integral Leech isometry has a lift in the rational Monster. -/
theorem liftSpinFrame_liftable (hsurj : Function.Surjective ι) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut ι hι hsurj := by
  obtain ⟨g, hg, _⟩ := liftLiftableOfChargeMatrix ι hι hsurj
    (liftGenSignedMatrix (liftSpinPerm ι hι hframe) (liftSpinSigns ι hι hframe))
    (liftSpinSigned_spec ι hι hframe)
  exact ⟨g, hg⟩

end FramePreserving

/-- The induced spin permutation for a Golay sign change. -/
def liftSpinGolayPerm (c : MonsterGriess.Code.C) : Equiv.Perm SpinIdx :=
  liftSpinPerm (liftGenGolay c) (liftGenGolay_isometry c) (fun _ h => liftSpinGolay_frame c h)

/-- The signs in the normalized Golay charge action. -/
def liftSpinGolaySigns (c : MonsterGriess.Code.C) : SpinIdx → ZMod 2 :=
  liftSpinSigns (liftGenGolay c) (liftGenGolay_isometry c) (fun _ h => liftSpinGolay_frame c h)

/-- The Golay row-permutation and rational-sign certificates, on all lattice vectors. -/
theorem liftSpinGolay_rows (c : MonsterGriess.Code.C) (α : leech.carrier) (i : SpinIdx) :
    let σ := liftSpinGolayPerm c
    let ε := liftSpinGolaySigns c
    let p := coordOfRed (red leech α)
    let q := coordOfRed (red leech (liftGenGolay c α))
    qPerm p.1 p.2 (σ i) = σ (qPerm q.1 q.2 i) ∧
      sgnR ℚ (ε i + qSign 0 p.1 p.2 (σ i)) =
        liftMonoWeight (liftGenGolay c) α *
          sgnR ℚ (qSign 0 q.1 q.2 i + ε (qPerm q.1 q.2 i)) :=
  liftSpinSigned_rows (liftGenGolay c) (liftGenGolay_isometry c)
    (fun _ h => liftSpinGolay_frame c h) α i

/-- The induced spin permutation for a Mathieu coordinate permutation. -/
def liftSpinMathieuPerm (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) :
    Equiv.Perm SpinIdx :=
  liftSpinPerm (liftGenMathieu σ hσ) (liftGenMathieu_isometry σ hσ)
    (fun _ h => liftSpinMathieu_frame σ hσ h)

/-- The signs in the normalized Mathieu charge action. -/
def liftSpinMathieuSigns (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) :
    SpinIdx → ZMod 2 :=
  liftSpinSigns (liftGenMathieu σ hσ) (liftGenMathieu_isometry σ hσ)
    (fun _ h => liftSpinMathieu_frame σ hσ h)

/-- The Mathieu row-permutation and rational-sign certificates, on all lattice vectors. -/
theorem liftSpinMathieu_rows (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ)
    (α : leech.carrier) (i : SpinIdx) :
    let τ := liftSpinMathieuPerm σ hσ
    let ε := liftSpinMathieuSigns σ hσ
    let p := coordOfRed (red leech α)
    let q := coordOfRed (red leech (liftGenMathieu σ hσ α))
    qPerm p.1 p.2 (τ i) = τ (qPerm q.1 q.2 i) ∧
      sgnR ℚ (ε i + qSign 0 p.1 p.2 (τ i)) =
        liftMonoWeight (liftGenMathieu σ hσ) α *
          sgnR ℚ (qSign 0 q.1 q.2 i + ε (qPerm q.1 q.2 i)) :=
  liftSpinSigned_rows (liftGenMathieu σ hσ) (liftGenMathieu_isometry σ hσ)
    (fun _ h => liftSpinMathieu_frame σ hσ h) α i

/-- Every Golay sign change, with the existing chosen VOA lift, is liftable. -/
theorem liftSpinGolay_liftable (c : MonsterGriess.Code.C) :
    ∃ g : liftableSubgroup, monsterLift g =
      liftTwVnatAut (liftGenGolay c) (liftGenGolay_isometry c) (liftGenGolay_surjective c) := by
  apply liftGenOfSignedBasis (liftGenGolay c) (liftGenGolay_isometry c)
    (liftGenGolay_surjective c) (liftSpinGolayPerm c) (liftSpinGolaySigns c)
  · intro j i
    exact (liftSpinGolay_rows c (latticeBasis leech j) i).1
  · intro j i
    exact (liftSpinGolay_rows c (latticeBasis leech j) i).2

/-- Every code-preserving coordinate permutation, with the existing chosen VOA lift,
is liftable; no choice of Mathieu generators is needed. -/
theorem liftSpinMathieu_liftable (σ : Equiv.Perm (Fin 24)) (hσ : liftGenPreservesCode σ) :
    ∃ g : liftableSubgroup, monsterLift g = liftTwVnatAut (liftGenMathieu σ hσ)
      (liftGenMathieu_isometry σ hσ) (liftGenMathieu_surjective σ hσ) := by
  apply liftGenOfSignedBasis (liftGenMathieu σ hσ) (liftGenMathieu_isometry σ hσ)
    (liftGenMathieu_surjective σ hσ) (liftSpinMathieuPerm σ hσ) (liftSpinMathieuSigns σ hσ)
  · intro j i
    exact (liftSpinMathieu_rows σ hσ (latticeBasis leech j) i).1
  · intro j i
    exact (liftSpinMathieu_rows σ hσ (latticeBasis leech j) i).2

end VOA.Moonshine.ConwayNorton.M8
