import VOA.Modules.ContragredientCharacterClose
import VOA.Modules.ZhuBijection

/-!
# Contragredient traces with the full ordinary-weight correction

The finite sum below is the zero-mode effect of `exp(L(1)) (-1)^L(0)`.
Unlike the quasi-primary formula it applies to every homogeneous insertion.
It does not yet identify this operation with square-bracket parity.
-/

namespace VOA.Huang.VerlindeRho

open VOA VertexOperatorAlgebra Module
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {W : VertexOperatorAlgebra V}
variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- The finite ordinary-weight contragredient correction. -/
noncomputable def contraState (W : VertexOperatorAlgebra V) (n : ℤ) (v : V) : V :=
  (-1 : ℂ) ^ n • ∑ j ∈ Finset.range (n.toNat + 1),
    ((j.factorial : ℂ)⁻¹) • ((W.L 1) ^ j) v

/-- The companion functional is the transpose of the corrected zero mode. -/
theorem dualCompMap_zeroMode (N : OrdVModule W M) {n : ℤ} {v : V}
    (hv : v ∈ W.grading n) (α : ℂ) (g : Module.Dual ℂ (N.weight α)) (x : M) :
    dualCompMap N n v (n - 1) α g x =
      g (internalProjTo N.isInternal α (oMod N (contraState W n v) x)) := by
  classical
  rw [dualCompMap_apply]
  simp only [contraState, map_smul, map_sum, LinearMap.smul_apply,
    LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [oMod_homogeneous N (L_one_pow_mem W hv j)]
  rw [show 2 * n - (n - 1) - 2 - (j : ℤ) = n - (j : ℤ) - 1 by omega]

/-- On each dual weight space the corrected zero mode is an actual transpose. -/
theorem oMod_contra_lof_general (N : OrdVModule W M) {n : ℤ} {v : V}
    (hv : v ∈ W.grading n) (α : ℂ) (g : Module.Dual ℂ (N.weight α)) :
    oMod (contragredientModule N) v
        (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g) =
      DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α
        (Module.Dual.transpose (weightBlock N (oMod N (contraState W n v)) α) g) := by
  classical
  rw [oMod_homogeneous (contragredientModule N) hv]
  change mode (YMdual N v) (n - 1) _ = _
  rw [mode_YMdual_homogeneous N hv, dualModeEndo_lof,
    show dualOutIdx n (n - 1) α = α by simp only [dualOutIdx]; push_cast; ring]
  congr 1
  apply LinearMap.ext
  intro x
  exact dualCompMap_zeroMode N hv α g x

/-- Blockwise transpose-conjugacy for an arbitrary homogeneous state. -/
theorem weightBlock_contra_general (N : OrdVModule W M) {n : ℤ} {v : V}
    (hv : v ∈ W.grading n) (α : ℂ) :
    weightBlock (contragredientModule N) (oMod (contragredientModule N) v) α =
      (lofEquiv N α).conj
        (Module.Dual.transpose (weightBlock N (oMod N (contraState W n v)) α)) := by
  classical
  apply LinearMap.ext
  intro y
  obtain ⟨g, rfl⟩ := (lofEquiv N α).surjective y
  change internalProjTo (contragredientModule N).isInternal α
    (oMod (contragredientModule N) v
      (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α g)) = _
  rw [oMod_contra_lof_general N hv]
  change internalProjTo (contragredient N (contragredientJacobi_holds N)).isInternal α
    (DirectSum.lof ℂ ℂ (fun β => Module.Dual ℂ (N.weight β)) α _) = _
  rw [internalProjTo_contra_lof]
  change _ = lofEquiv N α
    (Module.Dual.transpose (weightBlock N (oMod N (contraState W n v)) α)
      ((lofEquiv N α).symm (lofEquiv N α g)))
  rw [LinearEquiv.symm_apply_apply]

/-- The full coefficientwise contragredient trace identity, without quasi-primarity. -/
theorem onePoint_contragredient_general (N : OrdVModule W M) {n : ℤ} {v : V}
    (hv : v ∈ W.grading n) :
    onePoint (contragredientModule N) v = onePoint N (contraState W n v) := by
  funext e
  haveI := N.finrank (e + W.centralCharge / 24)
  haveI := (contragredientModule N).finrank (e + W.centralCharge / 24)
  change LinearMap.trace ℂ (RestrictedDual.weight N (e + W.centralCharge / 24))
    (weightBlock (contragredientModule N)
    (oMod (contragredientModule N) v) _) = _
  rw [weightBlock_contra_general N hv, LinearMap.trace_conj', LinearMap.trace_transpose']
  rfl

/-- The correction on a single ordinary weight space, bundled linearly. -/
noncomputable def contraStateLinear (W : VertexOperatorAlgebra V) (n : ℤ) : V →ₗ[ℂ] V :=
  (-1 : ℂ) ^ n • ∑ j ∈ Finset.range (n.toNat + 1),
    ((j.factorial : ℂ)⁻¹) • (W.L 1) ^ j

theorem contraStateLinear_apply (n : ℤ) (v : V) :
    contraStateLinear W n v = contraState W n v := by
  classical
  simp only [contraStateLinear, contraState, LinearMap.smul_apply, LinearMap.sum_apply]

/-- `exp(L(1)) (-1)^L(0)` on arbitrary states, assembled by ordinary weight. -/
noncomputable def contraTwist (W : VertexOperatorAlgebra V) : V →ₗ[ℂ] V :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (fun n => (contraStateLinear W n).comp (W.grading n).subtype)).comp
    (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem contraTwist_homogeneous {n : ℤ} {v : V} (hv : v ∈ W.grading n) :
    contraTwist W v = contraState W n v := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  change (DFinsupp.lsum ℂ (fun n => (contraStateLinear W n).comp (W.grading n).subtype))
    (DirectSum.decompose W.grading v) = _
  rw [DirectSum.decompose_of_mem W.grading hv]
  exact (DFinsupp.lsum_single ℂ
    (fun n => (contraStateLinear W n).comp (W.grading n).subtype) n ⟨v, hv⟩).trans
      (contraStateLinear_apply n v)

/-- Full formal contragredient trace identity for an arbitrary insertion. -/
theorem onePoint_contragredient_twist (N : OrdVModule W M) (v : V) :
    onePoint (contragredientModule N) v = onePoint N (contraTwist W v) := by
  have hv : v ∈ ⨆ n, W.grading n := by
    rw [W.isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction W.grading
    (motive := fun v => onePoint (contragredientModule N) v =
      onePoint N (contraTwist W v)) hv ?_ ?_ ?_
  · intro n v hv
    rw [contraTwist_homogeneous hv]
    exact onePoint_contragredient_general N hv
  · have hzero : ∀ {P : Type u} [AddCommGroup P] [Module ℂ P]
        (A : OrdVModule W P), onePoint A 0 = 0 := by
      intro P _ _ A
      simpa using onePoint_smul A 0 (0 : V)
    dsimp only
    rw [map_zero, hzero, hzero]
  · intro a b ha hb
    dsimp only at ha hb ⊢
    rw [map_add, onePoint_add, onePoint_add, ha, hb]

section Transport

variable {P : Type u} [AddCommGroup P] [Module ℂ P]
variable {A : OrdVModule W M} {B : OrdVModule W P}

/-- Restriction of a module equivalence to a weight space. -/
noncomputable def weightEquiv (e : ModuleEquiv W A B) (α : ℂ) :
    A.weight α ≃ₗ[ℂ] B.weight α where
  toFun x := ⟨e.toLinearEquiv x, e.maps_weight x.2⟩
  invFun x := ⟨e.toLinearEquiv.symm x, e.symm.maps_weight x.2⟩
  left_inv x := Subtype.ext (e.toLinearEquiv.symm_apply_apply x)
  right_inv x := Subtype.ext (e.toLinearEquiv.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add e.toLinearEquiv (x : M) (y : M))
  map_smul' c x := Subtype.ext (map_smul e.toLinearEquiv c (x : M))

/-- A module equivalence preserves every formal one-point trace. -/
theorem onePoint_equiv (e : ModuleEquiv W A B) (v : V) :
    onePoint A v = onePoint B v := by
  funext q
  let α := q + W.centralCharge / 24
  haveI := A.finrank α
  haveI := B.finrank α
  have hc : weightBlock B (oMod B v) α =
      (weightEquiv e α).conj (weightBlock A (oMod A v) α) := by
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (weightEquiv e α).surjective y
    change weightBlock B (oMod B v) α (weightEquiv e α x) =
      weightEquiv e α (weightBlock A (oMod A v) α
        ((weightEquiv e α).symm (weightEquiv e α x)))
    rw [LinearEquiv.symm_apply_apply]
    have hA := internalProjTo_coe A.isInternal α
      ⟨oMod A v x, oMod_preserves_lowest_all A v x.2⟩
    have hB := internalProjTo_coe B.isInternal α
      ⟨oMod B v (e.toLinearEquiv x),
        oMod_preserves_lowest_all B v (e.maps_weight x.2)⟩
    apply Subtype.ext
    change (internalProjTo B.isInternal α (oMod B v (e.toLinearEquiv x)) : P) =
      e.toLinearEquiv (internalProjTo A.isInternal α (oMod A v x))
    rw [hA, hB]
    exact (e.intertwine_oMod v x).symm
  change LinearMap.trace ℂ _ (weightBlock A (oMod A v) α) =
    LinearMap.trace ℂ _ (weightBlock B (oMod B v) α)
  rw [hc, LinearMap.trace_conj']

end Transport
end VOA.Huang.VerlindeRho
