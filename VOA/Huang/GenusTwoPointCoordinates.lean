import VOA.Huang.GenusTwoPointGrowth
import VOA.Modularity.ChangeCoord

/-!
# Coordinate operators on lowest-weight insertion modules

The positive Virasoro generator is pointwise finite and locally nilpotent.
Its exponential and the ordinary-weight exponential are genuine linear
equivalences on the algebraic module. The combined operator is defined on a
logarithmic coordinate, so its scaling law has no hidden branch assumption.

The coefficient family remains a parameter: this file does not construct the
iterative logarithm coefficients A_j of Huang's coordinate change. Nor does it
prove the intertwiner conjugation identity. Thus `coordinateModification` is
the operator construction needed for U, not an identification with Huang's U.
-/
namespace VOA.Huang.GenusTwoPoint
open VOA
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Filtration by ordinary levels, with integer indices for strict lowering. -/
noncomputable def moduleLevelLE (P : LWModule W) (d : ℤ) : Submodule ℂ P.carrier :=
  ⨆ j : {j : ℤ // j ≤ d}, P.isMod.weight (P.h + (j : ℤ))

theorem mem_moduleLevelLE (P : LWModule W) {j d : ℤ} (hjd : j ≤ d)
    {x : P.carrier} (hx : x ∈ P.isMod.weight (P.h + j)) : x ∈ moduleLevelLE P d :=
  Submodule.mem_iSup_of_mem (⟨j, hjd⟩ : {j : ℤ // j ≤ d}) hx

theorem moduleLevelLE_mono (P : LWModule W) {d e : ℤ} (h : d ≤ e) :
    moduleLevelLE P d ≤ moduleLevelLE P e :=
  iSup_le fun j => le_iSup_of_le (⟨(j : ℤ), le_trans j.2 h⟩ : {j : ℤ // j ≤ e}) le_rfl

theorem moduleLevelLE_eq_bot (P : LWModule W) {d : ℤ} (hd : d < 0) :
    moduleLevelLE P d = ⊥ := by
  refine le_antisymm (iSup_le fun j => ?_) bot_le
  rw [LWBottomRecovery.weight_neg_eq_bot P (by have := j.2; omega)]

theorem exists_mem_moduleLevelLE (P : LWModule W) (x : P.carrier) :
    ∃ d : ℤ, x ∈ moduleLevelLE P d := by
  refine FusionTop.induction_weight P.isMod x ⟨0, Submodule.zero_mem _⟩ ?_ ?_
  · intro x y hx hy
    obtain ⟨d, hd⟩ := hx
    obtain ⟨e, he⟩ := hy
    exact ⟨max d e, Submodule.add_mem _ (moduleLevelLE_mono P (le_max_left _ _) hd)
      (moduleLevelLE_mono P (le_max_right _ _) he)⟩
  · intro α y hy
    rcases FusionTop.eq_zero_or_level P hy with rfl | ⟨n, rfl⟩
    · exact ⟨0, Submodule.zero_mem _⟩
    · exact ⟨n, mem_moduleLevelLE P le_rfl (by simpa using hy)⟩

/-- `a k` is the coefficient of L(k+1). The sum is finite on each vector. -/
theorem moduleCoordGen_support_finite (P : LWModule W) (a : ℕ → ℂ) (x : P.carrier) :
    (Function.support fun k : ℕ =>
      a k • mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x).Finite := by
  obtain ⟨K, hK⟩ := P.isMod.truncation W.conformalVector x
  refine (Set.finite_Iio K.toNat).subset fun k hk => ?_
  simp only [Function.mem_support, Set.mem_Iio] at *
  by_contra hn
  exact hk (by rw [hK _ (by omega), smul_zero])

noncomputable def moduleCoordGen (P : LWModule W) (a : ℕ → ℂ) :
    Module.End ℂ P.carrier where
  toFun x := ∑ᶠ k : ℕ, a k • mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact finsum_add_distrib (moduleCoordGen_support_finite P a x)
      (moduleCoordGen_support_finite P a y)
  map_smul' c x := by
    change (∑ᶠ k : ℕ, a k • mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) (c • x)) =
      c • ∑ᶠ k : ℕ, a k • mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x
    rw [smul_finsum' c (moduleCoordGen_support_finite P a x)]
    exact finsum_congr fun k => by rw [map_smul, smul_comm]

theorem moduleCoordGen_mem_lower (P : LWModule W) (a : ℕ → ℂ) {d : ℤ}
    {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    moduleCoordGen P a x ∈ moduleLevelLE P (d - 1) := by
  induction hx using Submodule.iSup_induction' with
  | mem jj y hy =>
    have hf := moduleCoordGen_support_finite P a y
    change (∑ᶠ k : ℕ, _) ∈ _
    rw [finsum_eq_finsetSum_of_support_subset _
      (le_of_eq (Set.Finite.coe_toFinset hf).symm)]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    have hm := mode_mem_weight P.isMod W.conformal_mem hy ((k : ℤ) + 2)
    have he : P.h + ((jj : ℤ) : ℂ) + ((2 : ℤ) : ℂ) - (((k : ℤ) + 2 : ℤ) : ℂ) - 1 =
        P.h + (((jj : ℤ) - ((k : ℤ) + 1) : ℤ) : ℂ) := by push_cast; ring
    rw [he] at hm
    exact mem_moduleLevelLE P (by have := jj.2; omega) hm
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- No growth estimate, norm, or C₂ hypothesis is required for this exponential. -/
theorem moduleCoordGen_isLocNilp (P : LWModule W) (a : ℕ → ℂ) :
    IsLocNilp (moduleCoordGen P a) := by
  intro x
  obtain ⟨d, hd⟩ := exists_mem_moduleLevelLE P x
  have hpow : ∀ n : ℕ, ((moduleCoordGen P a) ^ n) x ∈ moduleLevelLE P (d - n) := by
    intro n
    induction n with
    | zero => simpa using hd
    | succ n ih =>
      rw [VOA.pow_succ'_apply]
      have hs := moduleCoordGen_mem_lower P a ih
      convert hs using 1
      congr 1
      push_cast
      ring
  refine ⟨(d + 1).toNat, ?_⟩
  have hs := hpow (d + 1).toNat
  rw [moduleLevelLE_eq_bot P (by omega : d - ((d + 1).toNat : ℤ) < 0)] at hs
  exact hs

/-- The finite exponential exp(-Σ a_k L(k+1)), including its inverse. -/
noncomputable def moduleCoordinateChange (P : LWModule W) (a : ℕ → ℂ) :
    P.carrier ≃ₗ[ℂ] P.carrier :=
  expEquiv (moduleCoordGen_isLocNilp P a).neg

theorem moduleCoordinateChange_of_primary (P : LWModule W) (a : ℕ → ℂ)
    {x : P.carrier}
    (hx : ∀ k : ℕ, mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x = 0) :
    moduleCoordinateChange P a x = x := by
  apply expFun_of_apply_eq_zero (moduleCoordGen_isLocNilp P a).neg
  change -(∑ᶠ k : ℕ, a k • mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x) = 0
  simp only [hx, smul_zero, finsum_zero, neg_zero]

section WeightExponential
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- exp(t L(0)) on an ordinary module, using its algebraic weight decomposition. -/
noncomputable def moduleWeightExp (A : OrdVModule W M) (t : ℂ) : Module.End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  (DFinsupp.lsum ℂ (fun α => Complex.exp (t * α) • (A.weight α).subtype)).comp
    (DirectSum.decomposeLinearEquiv A.weight).toLinearMap

theorem moduleWeightExp_of_weight (A : OrdVModule W M) (t : ℂ)
    {α : ℂ} {x : M} (hx : x ∈ A.weight α) :
    moduleWeightExp A t x = Complex.exp (t * α) • x := by
  letI := DirectSum.IsInternal.chooseDecomposition A.weight A.isInternal
  change (DFinsupp.lsum ℂ (fun α => Complex.exp (t * α) • (A.weight α).subtype))
    (DirectSum.decompose A.weight x) = _
  rw [DirectSum.decompose_of_mem A.weight hx]
  exact DFinsupp.lsum_single ℂ (fun α => Complex.exp (t * α) • (A.weight α).subtype)
    α ⟨x, hx⟩

theorem moduleWeightExp_add (A : OrdVModule W M) (s t : ℂ) (x : M) :
    moduleWeightExp A (s + t) x = moduleWeightExp A s (moduleWeightExp A t x) := by
  refine FusionTop.induction_weight A x (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro α y hy
    rw [moduleWeightExp_of_weight A _ hy, moduleWeightExp_of_weight A _ hy,
      map_smul, moduleWeightExp_of_weight A _ hy, smul_smul, add_mul, Complex.exp_add]
    rw [mul_comm]

theorem moduleWeightExp_zero (A : OrdVModule W M) (x : M) : moduleWeightExp A 0 x = x := by
  refine FusionTop.induction_weight A x (by simp) ?_ ?_
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro α y hy
    rw [moduleWeightExp_of_weight A _ hy]
    simp

noncomputable def moduleWeightExpEquiv (A : OrdVModule W M) (t : ℂ) : M ≃ₗ[ℂ] M where
  toLinearMap := moduleWeightExp A t
  invFun := moduleWeightExp A (-t)
  left_inv x := by
    change moduleWeightExp A (-t) (moduleWeightExp A t x) = x
    rw [← moduleWeightExp_add, neg_add_cancel, moduleWeightExp_zero]
  right_inv x := by
    change moduleWeightExp A t (moduleWeightExp A (-t) x) = x
    rw [← moduleWeightExp_add, add_neg_cancel, moduleWeightExp_zero]

end WeightExponential

/-- The chosen logarithm of 2πi in Huang's convention. -/
noncomputable def logTwoPiI : ℂ := Real.log (2 * Real.pi) + Complex.I * (Real.pi / 2)

/-- Operator construction for U(exp t), with its scalar coefficient family still
explicit. No coordinate-change identity for intertwiners is assumed. -/
noncomputable def coordinateModification (P : LWModule W) (a : ℕ → ℂ) (t : ℂ) :
    P.carrier ≃ₗ[ℂ] P.carrier :=
  (moduleCoordinateChange P a).trans (moduleWeightExpEquiv P.isMod (logTwoPiI + t))

/-- Scaling on the logarithmic cover, with no unrestricted principal-power law. -/
theorem coordinateModification_add (P : LWModule W) (a : ℕ → ℂ) (s t : ℂ)
    (x : P.carrier) :
    coordinateModification P a (s + t) x =
      moduleWeightExp P.isMod s (coordinateModification P a t x) := by
  change moduleWeightExp P.isMod (logTwoPiI + (s + t)) _ =
    moduleWeightExp P.isMod s (moduleWeightExp P.isMod (logTwoPiI + t) _)
  rw [← moduleWeightExp_add, show logTwoPiI + (s + t) = s + (logTwoPiI + t) by ring]

theorem coordinateModification_of_primary (P : LWModule W) (a : ℕ → ℂ) (t : ℂ)
    {α : ℂ} {x : P.carrier} (hx : x ∈ P.isMod.weight α)
    (hp : ∀ k : ℕ, mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x = 0) :
    coordinateModification P a t x = Complex.exp ((logTwoPiI + t) * α) • x := by
  change moduleWeightExp P.isMod (logTwoPiI + t) (moduleCoordinateChange P a x) = _
  rw [moduleCoordinateChange_of_primary P a hp, moduleWeightExp_of_weight P.isMod _ hx]

end VOA.Huang.GenusTwoPoint
