import VOA.Huang.GenusOneG1fSubstitution
import VOA.Huang.GenusOneG1eIndependence
import VOA.Huang.VerlindeVacuumFusion

/-!
# `TraceSkewInput`

`TraceSkew F hv c π` (`GenusOneG1eConjugation`) says that the Zhu traces of the bracket modes of
the two vacuum pairings `Y^π : M_b ⊗ M_a → V` and `Y^ε : M_a ⊗ M_b → V` are proportional, with
FHL's skew phase `e^{iπ(−n−1)}`. Proof:

1. *One-dimensionality.* `I(V / M_b M_a)` is finite-dimensional of dimension `≤ 1`
   (`vacuum_pairing_le_one`: the `A`-transform `I(V / M_b M_a) ↪ I(M_a' / M_b V')`,
   skew-symmetry, `V' ≅ V` (pseudo-unitarity, `contra_vacuum_equiv`) and the unit axiom
   `N^{M_a'}_{V M_b} ≤ 1`). Both `Y^π` and `Ω₀(Y^ε)` are nonzero members (`π ≠ 0` because
   `η ≫ π = 𝟙`, `ε ≠ 0`), so `Y^π = μ Ω₀(Y^ε)`, `μ ≠ 0` (`piInt_eq_smul_skew`).
2. *Transport.* By the proved substitution identity (`normalizedIntertwinerSubstitution_holds`)
   bracket modes are coordinate transports; `C_V L(−1) = L[−1] C_V`
   (`inverse_square_translation`), so `Y^π[w_b]_n w_a = μ e^{−iπ(n+1)}
   Σ_j ((−1)^j/j!) L[−1]^j Y^ε[w_a]_{n+j} w_b` (`bracketModes_skew`).
3. *Traces.* Zhu's one-point functions kill `L[−1]`-images (`torusOnePoint_Lsq_neg_one`), and
   are linear (`tfLin`), so only `j = 0` survives (`traceSkewInput_holds`).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open VOA VOA.Huang Complex CategoryTheory
open VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.VerlindeEigen
  VOA.Huang.ATransform VOA.Huang.FusionUnit VOA.Huang.HuangODEContra
  VOA.Huang.VerlindeVacuum VOA.Huang.TensorCat VOA.Huang.VerlindeTransport
open VOA.Huang.GenusTwoPoint (vacuumLW)
open VOA.Huang.FusionProduct (postcompose)
open VOA.Huang.GenusOneG1c (piInt epsInt)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1 The vacuum pairings form a space of dimension at most one -/

section Bound

variable {ι : Type w} [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι)

/-- **`I(V / M_b M_a)` is finite-dimensional of dimension `≤ 1`** (nice `V`). -/
theorem vacuum_pairing_le_one (hV : Nice W) (a b : ι) :
    FiniteDimensional ℂ (intertwiningSpace (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W))
      ∧ fusionRule (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W) ≤ 1 := by
  classical
  have hirrV : (adjointModule W).IsIrreducible :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.1.simple
  obtain ⟨e'⟩ := contra_vacuum_equiv hV (adjointModule W) hirrV (ModuleEquiv.refl _)
  let E : intertwiningSpace (D.Mfam b).isMod (contragredientModule (adjointModule W))
        (contragredientModule (D.Mfam a).isMod)
      ≃ₗ[ℂ] intertwiningSpace (adjointModule W) (D.Mfam b).isMod
        (contragredientModule (D.Mfam a).isMod) :=
    (BraidingSkew.skewEquiv _ _ _ BraidingSkew.omegaPhase_succ
      BraidingSkew.omegaPhase_ne_zero).trans (intertwiningEquivLeft e'.symm)
  have hP₂ := lwOf_irreducible D b
  have hP₃ : (contraLW (lwOf D a)).IsIrreducibleLW :=
    contraLW_isIrreducibleLW (lwOf_irreducible D a)
  haveI hfin : FiniteDimensional ℂ (intertwiningSpace (adjointModule W) (D.Mfam b).isMod
      (contragredientModule (D.Mfam a).isMod)) :=
    finiteDimensional_intertwiningSpace_adjoint (P₂ := lwOf D b) (P₃ := contraLW (lwOf D a))
      hP₂ hP₃
  haveI : FiniteDimensional ℂ (intertwiningSpace (D.Mfam b).isMod
      (contragredientModule (adjointModule W)) (contragredientModule (D.Mfam a).isMod)) :=
    LinearEquiv.finiteDimensional E.symm
  refine ⟨finiteDimensional_of_atrans _ _ _, ?_⟩
  calc fusionRule (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W)
      ≤ fusionRule (D.Mfam b).isMod (contragredientModule (adjointModule W))
          (contragredientModule (D.Mfam a).isMod) := fusionRule_le_atrans _ _ _
    _ = fusionRule (adjointModule W) (D.Mfam b).isMod (contragredientModule (D.Mfam a).isMod) :=
        E.finrank_eq
    _ ≤ 1 := fusionRule_adjoint_le_one (P₂ := lwOf D b) (P₃ := contraLW (lwOf D a)) hP₂ hP₃

end Bound

/-! ## §2 The two vacuum pairings are skew-proportional -/

section Pairing

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

theorem postcompose_eq_zero {F : FusionChoice W} {X Y T : Ordinary W} (f : tensorObj F X Y ⟶ T)
    (h : postcompose (F X Y).intertwiner T.isMod f = 0) : f = 0 := by
  rw [← TensorCat.lift_postcompose F f, h]
  have h0 : (0 : IntertwiningOperator X.isMod Y.isMod T.isMod) =
      postcompose (F X Y).intertwiner T.isMod (0 : tensorObj F X Y ⟶ T) :=
    (map_zero (postcompose (F X Y).intertwiner T.isMod)).symm
  rw [h0, TensorCat.lift_postcompose F]

theorem vacuumObject_id_ne_zero (hv : W.vacuum ≠ 0) :
    (𝟙 (vacuumObject : Ordinary W)) ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun f : (vacuumObject : Ordinary W) ⟶ vacuumObject => f.val W.vacuum) h
  simpa using this

/-- **`Y^π = μ Ω₀(Y^ε)` with `μ ≠ 0`.** -/
theorem piInt_eq_smul_skew (hV : Nice W) (F : FusionChoice W) {D : VOA.ModularData W ι} {a b : ι}
    (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (hπ : c.η ≫ π = 𝟙 _) :
    ∃ μ : ℂ, μ ≠ 0 ∧ (piInt F π).val = μ • BraidingSkew.skewModes
      (VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) BraidingSkew.omegaPhase
        (epsInt F c).val := by
  obtain ⟨hfin, hle⟩ := vacuum_pairing_le_one D hV a b
  let E := BraidingSkew.skewEquiv (D.Mfam a).isMod (D.Mfam b).isMod (adjointModule W)
    BraidingSkew.omegaPhase_succ BraidingSkew.omegaPhase_ne_zero
  have heps : (epsInt F c : intertwiningSpace (D.Mfam a).isMod (D.Mfam b).isMod
      (adjointModule W)) ≠ 0 := by
    intro h0
    exact c.ε_ne (postcompose_eq_zero c.ε h0)
  have hy0 : E (epsInt F c) ≠ 0 := (LinearEquiv.map_ne_zero_iff E).mpr heps
  have hpos : 0 < Module.finrank ℂ (intertwiningSpace (D.Mfam b).isMod (D.Mfam a).isMod
      (adjointModule W)) := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hy0⟩
  have h1 : Module.finrank ℂ (intertwiningSpace (D.Mfam b).isMod (D.Mfam a).isMod
      (adjointModule W)) = 1 := le_antisymm hle hpos
  obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hy0).mp h1
    (piInt F π : intertwiningSpace (D.Mfam b).isMod (D.Mfam a).isMod (adjointModule W))
  refine ⟨μ, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hμ
    have hπ0 : π = 0 := postcompose_eq_zero π hμ.symm
    rw [hπ0, Limits.comp_zero] at hπ
    exact vacuumObject_id_ne_zero hv hπ.symm
  · have := congrArg Subtype.val hμ
    rw [← this]
    rfl

end Pairing

/-! ## §3 Bracket modes and traces -/

section Trace

open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes transportedModes_apply
  inverse_square_translation)
open VOA.Huang.GenusTwoPoint.Separate (normalizedCoordinateChange)

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- `L[−1]` of the adjoint module is Zhu's `L[−1]`. -/
theorem sqL_adjoint_negOne (W : VertexOperatorAlgebra 𝒱) (x : 𝒱) :
    sqL (adjointModule W) (-1) x = Lsq W (-1) x := by
  rw [Lsq_apply, sqBracketCoeffZ_vacuum_of_ne ((-1) + 1) (by norm_num), mul_zero, zero_smul,
    sub_zero]
  simp only [sqL, if_neg (show (-1 : ℤ) ≠ -2 by norm_num), zero_smul, sub_zero]
  rfl

/-- Zhu's one-point functions kill `L[−1]`-images. -/
theorem traceFun_sqL_negOne (D : VOA.ModularData W ι) (x : ι) (v : 𝒱) (τ : UpperHalfPlane) :
    traceFun D.Mfam D.h x (sqL (adjointModule W) (-1) v) τ = 0 := by
  have h0 : torusOnePoint (D.Mfam x).isMod (sqL (adjointModule W) (-1) v) =
      torusOnePoint (D.Mfam x).isMod 0 := by
    rw [sqL_adjoint_negOne, torusOnePoint_Lsq_neg_one, ← torusOnePointHom_apply, map_zero]
  have hz := VOA.Huang.GenusOneG1e.traceFun_zero D x τ
  unfold traceFun at hz ⊢
  rw [h0]
  exact hz

theorem traceFun_sqL_negOne_pow (D : VOA.ModularData W ι) (x : ι) (v : 𝒱) (τ : UpperHalfPlane)
    (j : ℕ) : traceFun D.Mfam D.h x (((sqL (adjointModule W) (-1)) ^ (j + 1)) v) τ = 0 := by
  rw [pow_succ', Module.End.mul_apply]
  exact traceFun_sqL_negOne D x _ τ

/-- `C_V L(−1)^j = L[−1]^j C_V`. -/
theorem coordinateChange_Lm1_pow (hv : W.vacuum ≠ 0) (j : ℕ) (y : 𝒱) :
    normalizedCoordinateChange (vacuumLW W hv)
        (((VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) ^ j) y) =
      ((sqL (adjointModule W) (-1)) ^ j) (normalizedCoordinateChange (vacuumLW W hv) y) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    have h := inverse_square_translation (vacuumLW W hv)
      (normalizedCoordinateChange (vacuumLW W hv)
        (((VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) ^ j) y))
    rw [LinearEquiv.symm_apply_apply] at h
    have h2 := congrArg (normalizedCoordinateChange (vacuumLW W hv)) h
    rw [LinearEquiv.apply_symm_apply] at h2
    exact h2.symm

/-- Traces as a linear functional on the insertion. -/
theorem traceFun_linear (hV : Nice W) (D : VOA.ModularData W ι) (x : ι)
    (τ : UpperHalfPlane) : ∃ ℓ : 𝒱 →ₗ[ℂ] ℂ, ∀ v, ℓ v = traceFun D.Mfam D.h x v τ := by
  have hA : (adjointModule W).IsIrreducible :=
    (isSimple_iff_adjointModule_isIrreducible W).mp hV.1.simple
  refine ⟨VOA.Huang.GenusOneG1e.tfLin hV.1.c2Cofinite hA (moduleIntertwiner (lwOf D x).isMod)
    (D.hasWeight x) τ, fun v => ?_⟩
  rw [VOA.Huang.GenusOneG1e.tfLin_apply]
  exact VOA.Huang.GenusOne.IntCoord.vacuum_traceFunction_eq D x v τ

/-- **Trace-level skew-symmetry of bracket modes**, for any pair of vacuum pairings related by
`Y' = μ Ω₀(Y)`. -/
theorem traceFun_bracketModes_skew (hV : Nice W) (D : VOA.ModularData W ι) (hv : W.vacuum ≠ 0)
    {P Q : LWModule W} (Y : IntertwiningOperator P.isMod Q.isMod (adjointModule W))
    (Y' : IntertwiningOperator Q.isMod P.isMod (adjointModule W)) (μ : ℂ)
    (hY' : Y'.val = μ • BraidingSkew.skewModes
      (VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) BraidingSkew.omegaPhase Y.val)
    (n : ℂ) (wq : Q.carrier) (wp : P.carrier) (x : ι) (τ : UpperHalfPlane) :
    traceFun D.Mfam D.h x (bracketModes (N := vacuumLW W hv) Y' n wq wp) τ =
      μ * exp ((Real.pi : ℂ) * I * (-n - 1)) *
        traceFun D.Mfam D.h x (bracketModes (N := vacuumLW W hv) Y n wp wq) τ := by
  obtain ⟨ℓ, hℓ⟩ := traceFun_linear hV D x τ
  rw [← hℓ, ← hℓ, normalizedIntertwinerSubstitution_holds (N := vacuumLW W hv) Y' n wq wp,
    normalizedIntertwinerSubstitution_holds (N := vacuumLW W hv) Y n wp wq, transportedModes_apply,
    transportedModes_apply, hY']
  set wp' := (normalizedCoordinateChange P).symm wp
  set wq' := (normalizedCoordinateChange Q).symm wq
  have hT : BraidingSkew.Trunc Y.val :=
    BraidingSkew.trunc_of_isIntertwining Y.property
  obtain ⟨K, hK⟩ := hT.bound wp' wq' n
  change ℓ (normalizedCoordinateChange (vacuumLW W hv) (μ • BraidingSkew.skewModes
      (VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) BraidingSkew.omegaPhase Y.val
        n wq' wp')) = _
  let ℓC : 𝒱 →ₗ[ℂ] ℂ :=
    ℓ.comp ((normalizedCoordinateChange (vacuumLW W hv)).toLinearMap : 𝒱 →ₗ[ℂ] 𝒱)
  have hC : ∀ v : 𝒱, ℓ (normalizedCoordinateChange (vacuumLW W hv) v) = ℓC v := fun v => rfl
  rw [hC, hC]
  rw [BraidingSkew.skewModes_apply hT,
    BraidingSkew.sSum_eq_sum (K + 1) (fun j hj => hK j (by omega)), Finset.sum_range_succ',
    map_smul, map_smul, map_add, map_sum]
  have hz : ∀ j ∈ Finset.range K, ℓC
      (BraidingSkew.sTerm (VOA.SkewIntertwiner.Lm1 (adjointModule W).toWeakModule) Y.val n wp' wq'
        (j + 1)) = 0 := by
    intro j _
    rw [BraidingSkew.sTerm, map_smul, ← hC, coordinateChange_Lm1_pow, hℓ,
      traceFun_sqL_negOne_pow, smul_zero]
  rw [Finset.sum_eq_zero hz, zero_add, BraidingSkew.sTerm, pow_zero, Module.End.one_apply,
    map_smul, Nat.cast_zero, add_zero]
  simp only [BraidingSkew.sc, BraidingSkew.omegaPhase, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, mul_one, smul_eq_mul, one_mul]
  rw [show -(↑Real.pi * I) * (n + 1) = (Real.pi : ℂ) * I * (-n - 1) by ring, ← mul_assoc]
  rfl

/-- **`TraceSkewInput` is discharged** (given the proved substitution identity). -/
theorem traceSkewInput_holds : VOA.Huang.GenusOneG1e.TraceSkewInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D _ _ _ F a b c hv π hπ
  obtain ⟨μ, hμ, hrel⟩ := piInt_eq_smul_skew hNice F c hv π hπ
  exact ⟨μ, hμ, fun n wa wb x τ =>
    traceFun_bracketModes_skew hNice D hv (epsInt F c) (piInt F π) μ hrel n wb wa x τ⟩

end Trace

end VOA.Huang.GenusOneG1f
