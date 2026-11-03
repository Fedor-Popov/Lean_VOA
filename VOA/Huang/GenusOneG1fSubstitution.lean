import VOA.Huang.GenusOneG1fEnergy
import VOA.Huang.GenusTwoPointSepEnergyIdentity
import VOA.Huang.GenusOneG1eSharp

/-!
# The intertwiner coordinate-substitution identity (Huang 2005, Prop. 1.2)

For EVERY intertwining operator `Y` among lowest-weight modules,

  `bracketModes Y n w x = transportedModes Y n w x`

(`normalizedIntertwinerSubstitution_holds`): the independently defined explicit bracket
field `Y(e^{zL(0)} w, e^z − 1)` IS the actual coordinate transport
`C_N ∘ Y(C_P⁻¹ ·, ·) ∘ C_Q⁻¹`. This discharges `GenusOneG1e.IntertwinerSubstitutionInput`
(`intertwinerSubstitutionInput_holds`).

The proof transfers the mechanism of the module case (`normalizedSquareConjugation_of_zero`),
NOT a flow argument:

1. both fields satisfy the square energy commutator — the transported one by
   `transportedModes_energy`, the explicit one by the proved formal identity
   `bracketModes_energy` (`GenusOneG1fEnergy`);
2. on `C_P w`, `C_Q x` (`w, x` ordinary-homogeneous) both are `L[0]`-eigenvectors of eigenvalue
   `α + β − n − 1`, so is their difference `D`, hence `C_N⁻¹ D` is an `L(0)`-eigenvector of that
   eigenvalue;
3. both fields have the same leading term `Y_n w x` and are lower-triangular for the ordinary
   level filtration (the exponentials `C` are unipotent, the bracket coefficients have
   `b(α, n, 0) = 1` and all other terms `Y_{n+r}`, `r ≥ 1`, lower the level), so `C_N⁻¹ D` lies
   strictly below its own eigenvalue level, hence vanishes (`eigen_eq_zero_of_level`).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open VOA
open VOA.Huang.GenusOne (sqL)
open VOA.Huang.GenusOne.IntCoord (bracketModes bracketCoeff bracketModes_eq_sum_range
  transportedModes transportedModes_apply transportedModes_weight inverse_square_energy
  NormalizedIntertwinerSubstitution bracketCoeff_zero)
open VOA.Huang.GenusTwoPoint (moduleLevelLE mem_moduleLevelLE moduleLevelLE_mono
  exists_mem_moduleLevelLE)
open VOA.Huang.GenusTwoPoint.Separate (normalizedCoordinateChange
  normalizedModuleZeroConjugation_holds normalizedCoordinateChange_sub_mem_lower
  normalizedCoordinateChange_mem normalizedCoordinateChange_symm_mem)
open scoped BigOperators

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {P Q N : LWModule W}

/-! ## §1 The energy commutator and square weights of the explicit field -/

/-- **The bracket energy commutator, every insertion.** -/
theorem bracketModes_energy (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    sqL N.isMod 0 (bracketModes Y n w x) - bracketModes Y n w (sqL Q.isMod 0 x) =
      bracketModes Y n (sqL P.isMod 0 w) x - (n + 1) • bracketModes Y n w x := by
  refine FusionTop.induction_weight P.isMod w (by simp) ?_ ?_
  · intro w v hw hv
    simp only [map_add, LinearMap.add_apply, smul_add] at hw hv ⊢
    rw [show sqL N.isMod 0 (bracketModes Y n w x) + sqL N.isMod 0 (bracketModes Y n v x) -
        (bracketModes Y n w (sqL Q.isMod 0 x) + bracketModes Y n v (sqL Q.isMod 0 x)) =
        (sqL N.isMod 0 (bracketModes Y n w x) - bracketModes Y n w (sqL Q.isMod 0 x)) +
        (sqL N.isMod 0 (bracketModes Y n v x) - bracketModes Y n v (sqL Q.isMod 0 x)) by abel,
      hw, hv]
    abel
  · intro α w hw
    exact bracketModes_energy_of_weight Y hw n x

/-- **Square-weight grading of the explicit bracket field, unconditionally.** -/
theorem bracketModes_weight (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    {α β : ℂ} {w : P.carrier} {x : Q.carrier}
    (hw : sqL P.isMod 0 w = α • w) (hx : sqL Q.isMod 0 x = β • x) (n : ℂ) :
    sqL N.isMod 0 (bracketModes Y n w x) = (α + β - n - 1) • bracketModes Y n w x := by
  have h := bracketModes_energy Y n w x
  rw [hw, hx, map_smul, map_smul, LinearMap.smul_apply] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  module

/-! ## §2 Level filtrations -/

/-- An `L(0)`-eigenvector in a level truncation whose eigenvalue is not one of its levels
vanishes. -/
theorem eigen_eq_zero_of_level (P : LWModule W) {d : ℤ} {μ : ℂ}
    (hμ : ∀ j : ℤ, j ≤ d → μ ≠ P.h + j) {x : P.carrier} (hx : x ∈ moduleLevelLE P d)
    (he : mode (P.isMod.YM W.conformalVector) 1 x = μ • x) : x = 0 := by
  let D := mode (P.isMod.YM W.conformalVector) 1
  let S : Set ℂ := {α | α ≠ μ}
  have hdis : Disjoint (Module.End.eigenspace D μ)
      (⨆ α ∈ S, Module.End.eigenspace D α) :=
    (Module.End.eigenspaces_iSupIndep D).disjoint_biSup (by simp [S])
  have hsub : moduleLevelLE P d ≤ ⨆ α ∈ S, Module.End.eigenspace D α := by
    refine iSup_le fun j => ?_
    have hj : P.h + ((j : ℤ) : ℂ) ∈ S := by
      change P.h + ((j : ℤ) : ℂ) ≠ μ
      exact fun h => hμ j j.2 h.symm
    refine le_iSup_of_le (P.h + ((j : ℤ) : ℂ)) (le_iSup_of_le hj ?_)
    intro y hy
    exact Module.End.mem_eigenspace_iff.mpr (P.isMod.L0_weight _ _ hy)
  exact Submodule.disjoint_def.mp hdis _ (Module.End.mem_eigenspace_iff.mpr he) (hsub hx)

/-- Intertwiner modes respect the level filtrations, with the integral shift `κ`. -/
theorem intertwiner_mem_level (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) {n : ℂ} {κ : ℤ}
    (hκ : P.h + Q.h - n - 1 - N.h = κ) {a b : ℤ} {w : P.carrier} {x : Q.carrier}
    (hw : w ∈ moduleLevelLE P a) (hx : x ∈ moduleLevelLE Q b) (r : ℕ) :
    Y.val (n + r) w x ∈ moduleLevelLE N (a + b + κ - r) := by
  induction hw using Submodule.iSup_induction' with
  | mem j w hwj =>
    induction hx using Submodule.iSup_induction' with
    | mem l x hxl =>
      have hm := FusionTop.mem_weight Y.property hwj hxl (n + r)
      have he : P.h + ((j : ℤ) : ℂ) + (Q.h + ((l : ℤ) : ℂ)) - (n + r) - 1 =
          N.h + (((j : ℤ) + (l : ℤ) + κ - r : ℤ) : ℂ) := by
        push_cast; rw [← hκ]; ring
      rw [he] at hm
      exact mem_moduleLevelLE N (by have := j.2; have := l.2; omega) hm
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add w v _ _ hw hv => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hw hv

/-- The explicit bracket field is the plain mode up to strictly lower levels. -/
theorem bracketModes_sub_mem_lower (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) {n : ℂ}
    {κ : ℤ} (hκ : P.h + Q.h - n - 1 - N.h = κ) {a b : ℤ} {w : P.carrier} {x : Q.carrier}
    (hw : w ∈ moduleLevelLE P a) (hx : x ∈ moduleLevelLE Q b) :
    bracketModes Y n w x - Y.val n w x ∈ moduleLevelLE N (a + b + κ - 1) := by
  induction hw using Submodule.iSup_induction' with
  | mem j w hwj =>
    obtain ⟨R, hR⟩ := intertwiner_nat_bound Y n w x
    rw [bracketModes_eq_sum_range Y hwj n x (R + 1) (fun r hr => hR r (by omega)),
      Finset.sum_range_succ', bracketCoeff_zero, one_smul, Nat.cast_zero, add_zero,
      add_sub_cancel_right]
    refine Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_
    have h := intertwiner_mem_level Y hκ (mem_moduleLevelLE P le_rfl hwj) hx (r + 1)
    exact moduleLevelLE_mono N (by have := j.2; push_cast; omega) h
  | zero => simp
  | add w v _ _ hw hv =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply,
      show bracketModes Y n w x + bracketModes Y n v x - (Y.val n w x + Y.val n v x) =
        (bracketModes Y n w x - Y.val n w x) + (bracketModes Y n v x - Y.val n v x) by abel]
    exact Submodule.add_mem _ hw hv

/-! ## §3 The substitution identity -/

/-- **The sandwich identity on ordinary-homogeneous vectors.** -/
theorem sandwich_of_weight (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) {α β : ℂ}
    {w : P.carrier} {x : Q.carrier} (hw : w ∈ P.isMod.weight α) (hx : x ∈ Q.isMod.weight β)
    (n : ℂ) :
    normalizedCoordinateChange N (Y.val n w x) =
      bracketModes Y n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) := by
  rcases FusionTop.eq_zero_or_level P hw with rfl | ⟨a, rfl⟩
  · simp
  rcases FusionTop.eq_zero_or_level Q hx with rfl | ⟨b, rfl⟩
  · simp
  apply sub_eq_zero.mp
  apply (normalizedCoordinateChange N).symm.injective
  rw [map_zero]
  -- square weights
  have hCw : sqL P.isMod 0 (normalizedCoordinateChange P w) =
      (P.h + a) • normalizedCoordinateChange P w := by
    rw [normalizedModuleZeroConjugation_holds P w, P.isMod.L0_weight _ w hw, map_smul]
  have hCx : sqL Q.isMod 0 (normalizedCoordinateChange Q x) =
      (Q.h + b) • normalizedCoordinateChange Q x := by
    rw [normalizedModuleZeroConjugation_holds Q x, Q.isMod.L0_weight _ x hx, map_smul]
  have hT : normalizedCoordinateChange N (Y.val n w x) = transportedModes Y n
      (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) := by
    rw [transportedModes_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hTw := transportedModes_weight Y hCw hCx n
  have hBw := bracketModes_weight Y hCw hCx n
  rw [← hT] at hTw
  set D := normalizedCoordinateChange N (Y.val n w x) -
    bracketModes Y n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) with hD
  have hDw : sqL N.isMod 0 D = ((P.h + a) + (Q.h + b) - n - 1) • D := by
    rw [hD, map_sub, hTw, hBw, smul_sub]
  have hDe : mode (N.isMod.YM W.conformalVector) 1 ((normalizedCoordinateChange N).symm D) =
      ((P.h + a) + (Q.h + b) - n - 1) • (normalizedCoordinateChange N).symm D := by
    rw [← inverse_square_energy N D, hDw, map_smul]
  by_cases hδ : ∃ κ : ℤ, P.h + Q.h - n - 1 - N.h = κ
  · obtain ⟨κ, hκ⟩ := hδ
    have hwa : w ∈ moduleLevelLE P a := mem_moduleLevelLE P le_rfl (by simpa using hw)
    have hxb : x ∈ moduleLevelLE Q b := mem_moduleLevelLE Q le_rfl (by simpa using hx)
    have hy : Y.val n w x ∈ moduleLevelLE N (a + b + κ) := by
      have := intertwiner_mem_level Y hκ hwa hxb 0
      simpa using this
    have t1 := normalizedCoordinateChange_sub_mem_lower N hy
    have hw1 : w - normalizedCoordinateChange P w ∈ moduleLevelLE P (a - 1) := by
      have := Submodule.neg_mem _ (normalizedCoordinateChange_sub_mem_lower P hwa)
      simpa using this
    have hx1 : x - normalizedCoordinateChange Q x ∈ moduleLevelLE Q (b - 1) := by
      have := Submodule.neg_mem _ (normalizedCoordinateChange_sub_mem_lower Q hxb)
      simpa using this
    have t2a : Y.val n (w - normalizedCoordinateChange P w) x ∈
        moduleLevelLE N (a + b + κ - 1) := by
      have := intertwiner_mem_level Y hκ hw1 hxb 0
      simp only [Nat.cast_zero, add_zero, sub_zero] at this
      exact moduleLevelLE_mono N (by omega) this
    have t2b : Y.val n (normalizedCoordinateChange P w) (x - normalizedCoordinateChange Q x) ∈
        moduleLevelLE N (a + b + κ - 1) := by
      have := intertwiner_mem_level Y hκ (normalizedCoordinateChange_mem P hwa) hx1 0
      simp only [Nat.cast_zero, add_zero, sub_zero] at this
      exact moduleLevelLE_mono N (by omega) this
    have t3 := Submodule.neg_mem _ (bracketModes_sub_mem_lower Y hκ
      (normalizedCoordinateChange_mem P hwa) (normalizedCoordinateChange_mem Q hxb))
    have hsum : D = (normalizedCoordinateChange N (Y.val n w x) - Y.val n w x) +
        (Y.val n (w - normalizedCoordinateChange P w) x +
          Y.val n (normalizedCoordinateChange P w) (x - normalizedCoordinateChange Q x)) +
        -(bracketModes Y n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) -
          Y.val n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x)) := by
      rw [hD, map_sub, map_sub, LinearMap.sub_apply]
      abel
    have hDmem : D ∈ moduleLevelLE N (a + b + κ - 1) := by
      rw [hsum]
      exact Submodule.add_mem _ (Submodule.add_mem _ t1 (Submodule.add_mem _ t2a t2b)) t3
    refine eigen_eq_zero_of_level N (d := a + b + κ - 1) ?_
      (normalizedCoordinateChange_symm_mem N hDmem) hDe
    intro j hj hjeq
    have : ((a + b + κ : ℤ) : ℂ) = (j : ℂ) := by
      push_cast
      linear_combination hjeq - hκ
    have := Int.cast_injective (α := ℂ) this
    omega
  · obtain ⟨d, hd⟩ := exists_mem_moduleLevelLE N D
    refine eigen_eq_zero_of_level N (d := d) ?_ (normalizedCoordinateChange_symm_mem N hd) hDe
    intro j _ hjeq
    apply hδ
    refine ⟨j - a - b, ?_⟩
    push_cast
    linear_combination hjeq

/-- **The sandwich identity**, every insertion. -/
theorem sandwich (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) (n : ℂ) (w : P.carrier)
    (x : Q.carrier) :
    normalizedCoordinateChange N (Y.val n w x) =
      bracketModes Y n (normalizedCoordinateChange P w) (normalizedCoordinateChange Q x) := by
  refine FusionTop.induction_weight P.isMod w (by simp) ?_ ?_
  · intro w v hw hv
    simp only [map_add, LinearMap.add_apply, hw, hv]
  · intro α w hw
    refine FusionTop.induction_weight Q.isMod x (by simp) ?_ ?_
    · intro x y hx hy
      simp only [map_add, hx, hy]
    · intro β x hx
      exact sandwich_of_weight Y hw hx n

/-- **Huang's coordinate substitution for intertwining operators (math/0303049,
Prop. 1.2) for every intertwiner among lowest-weight modules.** -/
theorem normalizedIntertwinerSubstitution_holds
    (Y : IntertwiningOperator P.isMod Q.isMod N.isMod) : NormalizedIntertwinerSubstitution Y := by
  intro n w x
  have h := sandwich Y n ((normalizedCoordinateChange P).symm w)
    ((normalizedCoordinateChange Q).symm x)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  rw [transportedModes_apply, h]

/-- **`IntertwinerSubstitutionInput` is discharged.** -/
theorem intertwinerSubstitutionInput_holds :
    VOA.Huang.GenusOneG1e.IntertwinerSubstitutionInput.{u} := by
  intro 𝒱 _ _ W _ P₁ P₂ Q _ _ _ Y
  exact normalizedIntertwinerSubstitution_holds Y

end VOA.Huang.GenusOneG1f
