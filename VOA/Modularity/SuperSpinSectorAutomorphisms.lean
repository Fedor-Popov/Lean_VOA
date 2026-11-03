/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Modularity.SuperSpinRelations
import VOA.Core.SuperAutomorphism

/-!
# State eigenspaces for one fixed pair of commuting involutions

Fix an **outer** ordered pair `(g,h)` of commuting even involutions.  This file constructs the
four simultaneous state eigenspaces for that fixed pair, indexed by `SpinPair`, using

`P_(mu,lambda) = (1 + mu g)(1 + lambda h) / 4`.

The `SpinPair` index is an **inner state-eigencharacter label**: it records the eigenvalues of a
state under the already fixed `g` and `h`.  It is not an outer trace-sector label, does not choose
a `g`-twisted module or an `h`-intertwiner, and does not enumerate the commuting pairs in an
automorphism group.  A different outer pair `(g,h)` produces a different decomposition.

The projectors are mutually orthogonal and sum to the identity, giving a constructive internal
direct sum.  They preserve ordinary conformal weight and parity separately, with no
spin--statistics assumption.  This file deliberately imports neither `SuperSpinDescent`
(whose translation premise is false in general) nor any C2/descent interface built on it.
-/

namespace VOA

open scoped BigOperators

set_option autoImplicit false

universe u

variable {VType : Type u} [AddCommGroup VType] [Module Complex VType]
variable {W : SuperVertexOperatorAlgebra VType}

namespace SuperAut

/-- The linear endomorphism underlying a super-VOA automorphism. -/
def toEnd (g : SuperAut W) : Module.End Complex VType := g.toLinearEquiv.toLinearMap

@[simp] theorem toEnd_apply (g : SuperAut W) (x : VType) : g.toEnd x = g x := rfl

/-- The projector `(1 + mu g)/2` onto the `mu` eigenspace of an involution. -/
noncomputable def spinProjector (g : SuperAut W) (mu : SpinPhase) :
    Module.End Complex VType :=
  (2 : Complex)⁻¹ • (LinearMap.id + SpinPhase.value mu • g.toEnd)

@[simp] theorem spinProjector_apply (g : SuperAut W) (mu : SpinPhase) (x : VType) :
    g.spinProjector mu x =
      (2 : Complex)⁻¹ • (x + SpinPhase.value mu • g x) := by
  simp [spinProjector, toEnd]

theorem spinPhase_value_sq (mu : SpinPhase) : SpinPhase.value mu ^ 2 = 1 := by
  rcases zmod2_cases mu with rfl | rfl <;>
    norm_num [SpinPhase.value, SpinPhase.plus]

theorem spinPhase_value_ne {mu nu : SpinPhase} (h : mu ≠ nu) :
    SpinPhase.value mu = -SpinPhase.value nu := by
  rcases zmod2_cases mu with rfl | rfl <;>
    rcases zmod2_cases nu with rfl | rfl
  · exact (h rfl).elim
  · norm_num [SpinPhase.value, SpinPhase.plus]
  · norm_num [SpinPhase.value, SpinPhase.plus]
  · exact (h rfl).elim

theorem apply_apply_eq_of_sq_one (g : SuperAut W) (hg : g ^ 2 = 1) (x : VType) :
    g (g x) = x := by
  have hx := congrArg (fun a : SuperAut W => a x) hg
  simpa [pow_two] using hx

theorem apply_comm_of_comm (g h : SuperAut W) (hcomm : g * h = h * g) (x : VType) :
    g (h x) = h (g x) := by
  exact congrArg (fun a : SuperAut W => a x) hcomm

/-- An involution projector lands in the advertised eigenspace. -/
theorem map_spinProjector (g : SuperAut W) (hg : g ^ 2 = 1)
    (mu : SpinPhase) (x : VType) :
    g (g.spinProjector mu x) = SpinPhase.value mu • g.spinProjector mu x := by
  rw [spinProjector_apply, g.toLinearEquiv.map_smul, g.toLinearEquiv.map_add,
    g.toLinearEquiv.map_smul, g.apply_apply_eq_of_sq_one hg]
  rcases zmod2_cases mu with rfl | rfl <;>
    norm_num [SpinPhase.value, SpinPhase.plus, SpinPhase.minus] <;> module

/-- A projector is the identity on its eigenspace. -/
theorem spinProjector_eq_self (g : SuperAut W) {mu : SpinPhase} {x : VType}
    (hx : g x = SpinPhase.value mu • x) : g.spinProjector mu x = x := by
  rw [spinProjector_apply, hx]
  rcases zmod2_cases mu with rfl | rfl <;>
    norm_num [SpinPhase.value, SpinPhase.plus, SpinPhase.minus] <;> module

/-- The opposite projector kills an eigenvector. -/
theorem spinProjector_eq_zero_of_ne (g : SuperAut W) {mu nu : SpinPhase} (h : mu ≠ nu)
    {x : VType} (hx : g x = SpinPhase.value nu • x) :
    g.spinProjector mu x = 0 := by
  rcases zmod2_cases mu with rfl | rfl <;>
    rcases zmod2_cases nu with rfl | rfl
  · exact (h rfl).elim
  · rw [spinProjector_apply, hx]
    norm_num [SpinPhase.value, SpinPhase.plus, SpinPhase.minus]
  · rw [spinProjector_apply, hx]
    norm_num [SpinPhase.value, SpinPhase.plus, SpinPhase.minus]
  · exact (h rfl).elim

/-- The two eigenspace projectors sum to the identity. -/
theorem sum_spinProjector (g : SuperAut W) (x : VType) :
    ∑ mu : SpinPhase, g.spinProjector mu x = x := by
  rw [show (Finset.univ : Finset SpinPhase) =
      {SpinPhase.plus, SpinPhase.minus} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [spinProjector_apply]
  norm_num [SpinPhase.value, SpinPhase.plus, SpinPhase.minus]
  module

/-- The simultaneous quarter-projector for one fixed outer pair.  The `h` projector acts first. -/
noncomputable def spinPairProjector (g h : SuperAut W) (p : SpinPair) :
    Module.End Complex VType :=
  (g.spinProjector p.mu).comp (h.spinProjector p.lambda)

@[simp] theorem spinPairProjector_apply (g h : SuperAut W) (p : SpinPair) (x : VType) :
    spinPairProjector g h p x = g.spinProjector p.mu (h.spinProjector p.lambda x) := rfl

/-- A projector for one involution commutes with the other commuting involution. -/
theorem map_spinProjector_comm (g h : SuperAut W) (hcomm : g * h = h * g)
    (mu : SpinPhase) (x : VType) :
    g (h.spinProjector mu x) = h.spinProjector mu (g x) := by
  rw [spinProjector_apply, g.toLinearEquiv.map_smul, g.toLinearEquiv.map_add,
    g.toLinearEquiv.map_smul, spinProjector_apply, g.apply_comm_of_comm h hcomm]

/-- A simultaneous projector lands in the first eigenspace. -/
theorem map_spinPairProjector_fst (g h : SuperAut W) (hg : g ^ 2 = 1)
    (_hcomm : g * h = h * g) (p : SpinPair) (x : VType) :
    g (spinPairProjector g h p x) =
      SpinPhase.value p.mu • spinPairProjector g h p x := by
  exact g.map_spinProjector hg p.mu (h.spinProjector p.lambda x)

/-- A simultaneous projector lands in the second eigenspace. -/
theorem map_spinPairProjector_snd (g h : SuperAut W) (hh : h ^ 2 = 1)
    (hcomm : g * h = h * g) (p : SpinPair) (x : VType) :
    h (spinPairProjector g h p x) =
      SpinPhase.value p.lambda • spinPairProjector g h p x := by
  rw [spinPairProjector_apply, h.map_spinProjector_comm g hcomm.symm,
    h.map_spinProjector hh, (g.spinProjector p.mu).map_smul]

/-- The four inner state eigenspaces for one fixed outer pair `(g,h)`. -/
noncomputable def spinSectors (g h : SuperAut W) :
    SuperNearVOA.SuperSpinSectors (VType := VType) :=
  fun p => LinearMap.range (spinPairProjector g h p)

theorem mem_spinSectors_iff (g h : SuperAut W) (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hcomm : g * h = h * g) (p : SpinPair) (x : VType) :
    x ∈ spinSectors g h p ↔
      g x = SpinPhase.value p.mu • x ∧ h x = SpinPhase.value p.lambda • x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨g.map_spinPairProjector_fst h hg hcomm p y,
      g.map_spinPairProjector_snd h hh hcomm p y⟩
  · rintro ⟨hgx, hhx⟩
    refine ⟨x, ?_⟩
    rw [spinPairProjector_apply, h.spinProjector_eq_self hhx,
      g.spinProjector_eq_self hgx]

/-- A simultaneous projector acts as the identity on its own inner eigenspace. -/
theorem spinPairProjector_eq_self (g h : SuperAut W) (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hcomm : g * h = h * g) {p : SpinPair} {x : VType}
    (hx : x ∈ spinSectors g h p) : spinPairProjector g h p x = x := by
  rw [mem_spinSectors_iff g h hg hh hcomm] at hx
  rw [spinPairProjector_apply, h.spinProjector_eq_self hx.2,
    g.spinProjector_eq_self hx.1]

/-- Distinct simultaneous projectors are orthogonal on inner eigenspace vectors. -/
theorem spinPairProjector_eq_zero_of_ne (g h : SuperAut W) (hg : g ^ 2 = 1)
    (hh : h ^ 2 = 1) (hcomm : g * h = h * g) {p q : SpinPair} (hpq : p ≠ q)
    {x : VType} (hx : x ∈ spinSectors g h q) : spinPairProjector g h p x = 0 := by
  rw [mem_spinSectors_iff g h hg hh hcomm] at hx
  by_cases hlambda : p.lambda = q.lambda
  · have hmu : p.mu ≠ q.mu := fun hmu => hpq (SpinPair.ext hmu hlambda)
    rw [spinPairProjector_apply, h.spinProjector_eq_self (hlambda ▸ hx.2),
      g.spinProjector_eq_zero_of_ne hmu hx.1]
  · rw [spinPairProjector_apply,
      h.spinProjector_eq_zero_of_ne hlambda hx.2, map_zero]

/-- The four quarter-projectors sum to the identity. -/
theorem sum_spinPairProjector (g h : SuperAut W) (x : VType) :
    ∑ p : SpinPair, spinPairProjector g h p x = x := by
  rw [show (Finset.univ : Finset SpinPair) =
      {SpinPair.pp, SpinPair.pm, SpinPair.mp, SpinPair.mm} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [spinPairProjector_apply]
  norm_num [SpinPair.pp, SpinPair.pm, SpinPair.mp, SpinPair.mm, spinProjector_apply,
    SpinPhase.value, SpinPhase.plus, SpinPhase.minus]
  module

/-! ## Constructive direct-sum decomposition -/

/-- A pair projector with its codomain restricted to its range eigenspace. -/
noncomputable def spinPairProjectorToSector (g h : SuperAut W) (p : SpinPair) :
    VType →ₗ[Complex] spinSectors g h p :=
  (spinPairProjector g h p).codRestrict (spinSectors g h p)
    (fun x => ⟨x, rfl⟩)

@[simp] theorem spinPairProjectorToSector_coe (g h : SuperAut W) (p : SpinPair)
    (x : VType) :
    (spinPairProjectorToSector g h p x : VType) = spinPairProjector g h p x := rfl

/-- The four projector components, regarded as a linear map into a finite dependent product. -/
noncomputable def spinSectorComponents (g h : SuperAut W) :
    VType →ₗ[Complex] ((p : SpinPair) → spinSectors g h p) where
  toFun x p := spinPairProjectorToSector g h p x
  map_add' x y := by
    funext p
    exact (spinPairProjectorToSector g h p).map_add x y
  map_smul' c x := by
    funext p
    exact (spinPairProjectorToSector g h p).map_smul c x

/-- The explicit decomposition map `x ↦ (P_p x)_p`. -/
noncomputable def spinSectorDecompose (g h : SuperAut W) :
    VType →ₗ[Complex] DirectSum SpinPair (fun p => spinSectors g h p) :=
  (DirectSum.linearEquivFunOnFintype Complex SpinPair
    (fun p => spinSectors g h p)).symm.toLinearMap.comp (spinSectorComponents g h)

theorem spinSectorDecompose_eq_sum_lof (g h : SuperAut W) (x : VType) :
    spinSectorDecompose g h x =
      ∑ p : SpinPair, DirectSum.lof Complex SpinPair (fun q => spinSectors g h q) p
        (spinPairProjectorToSector g h p x) := by
  classical
  apply (DirectSum.linearEquivFunOnFintype Complex SpinPair
    (fun p => spinSectors g h p)).injective
  funext p
  simp only [spinSectorDecompose, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_sum, DirectSum.linearEquivFunOnFintype_lof,
    Finset.sum_apply]
  change spinPairProjectorToSector g h p x =
    ∑ q, Pi.single q (spinPairProjectorToSector g h q x) p
  symm
  simp [Finset.sum_pi_single]

theorem coeLinearMap_spinSectorDecompose (g h : SuperAut W) (x : VType) :
    DirectSum.coeLinearMap (spinSectors g h) (spinSectorDecompose g h x) = x := by
  rw [spinSectorDecompose_eq_sum_lof, map_sum]
  simp only [DirectSum.coeLinearMap_lof, spinPairProjectorToSector_coe]
  exact sum_spinPairProjector g h x

@[simp] theorem spinSectorDecompose_component (g h : SuperAut W) (p : SpinPair) (x : VType) :
    spinSectorDecompose g h x p = spinPairProjectorToSector g h p x := by
  classical
  change (DirectSum.linearEquivFunOnFintype Complex SpinPair
    (fun q => spinSectors g h q) (spinSectorDecompose g h x)) p = _
  have happly := (DirectSum.linearEquivFunOnFintype Complex SpinPair
    (fun q => spinSectors g h q)).apply_symm_apply (spinSectorComponents g h x)
  exact congrFun happly p

/-- On a vector already in one eigenspace, the decomposition has one nonzero component. -/
theorem spinSectorDecompose_of_mem (g h : SuperAut W) (hg : g ^ 2 = 1)
    (hh : h ^ 2 = 1) (hcomm : g * h = h * g) {p : SpinPair} {x : VType}
    (hx : x ∈ spinSectors g h p) :
    spinSectorDecompose g h x =
      DirectSum.lof Complex SpinPair (fun q => spinSectors g h q) p ⟨x, hx⟩ := by
  classical
  apply (DirectSum.linearEquivFunOnFintype Complex SpinPair
    (fun q => spinSectors g h q)).injective
  funext q
  by_cases hqp : q = p
  · subst q
    apply Subtype.ext
    simp [spinPairProjector_eq_self g h hg hh hcomm hx]
  · apply Subtype.ext
    change ((spinSectorDecompose g h x q : spinSectors g h q) : VType) =
      (((DirectSum.lof Complex SpinPair (fun r => spinSectors g h r) p ⟨x, hx⟩) q :
        spinSectors g h q) : VType)
    rw [spinSectorDecompose_component]
    rw [spinPairProjectorToSector_coe,
      spinPairProjector_eq_zero_of_ne g h hg hh hcomm hqp hx]
    rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne p q _ hqp]
    rfl

/-- The quarter-projectors give an internal direct sum of the four simultaneous eigenspaces. -/
@[reducible] noncomputable def spinSectorsDecomposition (g h : SuperAut W) (hg : g ^ 2 = 1)
    (hh : h ^ 2 = 1) (hcomm : g * h = h * g) :
    DirectSum.Decomposition (spinSectors g h) := by
  apply DirectSum.Decomposition.ofLinearMap (spinSectors g h) (spinSectorDecompose g h)
  · apply LinearMap.ext
    intro x
    exact coeLinearMap_spinSectorDecompose g h x
  · apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    simpa [LinearMap.comp_apply] using spinSectorDecompose_of_mem g h hg hh hcomm x.2

/-! ## Ordinary weight and parity compatibility -/

/-- Each involution projector preserves every ordinary conformal-weight subspace. -/
theorem spinProjector_mem_grading (g : SuperAut W) (mu : SpinPhase) {k : Complex}
    {x : VType} (hx : x ∈ W.grading k) : g.spinProjector mu x ∈ W.grading k := by
  rw [spinProjector_apply]
  exact (W.grading k).smul_mem _ ((W.grading k).add_mem hx
    ((W.grading k).smul_mem _ (g.map_mem_grading hx)))

/-- Simultaneous projectors preserve ordinary conformal weight. -/
theorem spinPairProjector_mem_grading (g h : SuperAut W) (p : SpinPair) {k : Complex}
    {x : VType} (hx : x ∈ W.grading k) : spinPairProjector g h p x ∈ W.grading k := by
  exact g.spinProjector_mem_grading p.mu (h.spinProjector_mem_grading p.lambda hx)

/-- Each involution projector preserves parity independently of conformal weight. -/
theorem spinProjector_mem_parity (g : SuperAut W) (mu : SpinPhase) {r : ZMod 2}
    {x : VType} (hx : x ∈ W.parity r) : g.spinProjector mu x ∈ W.parity r := by
  rw [spinProjector_apply]
  exact (W.parity r).smul_mem _ ((W.parity r).add_mem hx
    ((W.parity r).smul_mem _ (g.map_mem_parity hx)))

/-- Simultaneous projectors preserve parity, with no spin--statistics hypothesis. -/
theorem spinPairProjector_mem_parity (g h : SuperAut W) (p : SpinPair) {r : ZMod 2}
    {x : VType} (hx : x ∈ W.parity r) : spinPairProjector g h p x ∈ W.parity r := by
  exact g.spinProjector_mem_parity p.mu (h.spinProjector_mem_parity p.lambda hx)

/-- Under the explicit decomposition, `homogProj` is the quarter-projector. -/
theorem homogProj_spinSectors (g h : SuperAut W) (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (hcomm : g * h = h * g) (p : SpinPair) (x : VType) :
    letI := spinSectorsDecomposition g h hg hh hcomm
    homogProj (spinSectors g h) p x = spinPairProjector g h p x := by
  letI := spinSectorsDecomposition g h hg hh hcomm
  rw [homogProj_apply]
  change ((spinSectorDecompose g h x) p : VType) = _
  simp

/-- Sector projection also preserves parity, separately from conformal weight. -/
theorem homogProj_spinSectors_mem_parity (g h : SuperAut W) (hg : g ^ 2 = 1)
    (hh : h ^ 2 = 1) (hcomm : g * h = h * g) {r : ZMod 2} (p : SpinPair)
    {x : VType} (hx : x ∈ W.parity r) :
    letI := spinSectorsDecomposition g h hg hh hcomm
    homogProj (spinSectors g h) p x ∈ W.parity r := by
  letI := spinSectorsDecomposition g h hg hh hcomm
  rw [homogProj_spinSectors g h hg hh hcomm]
  exact spinPairProjector_mem_parity g h p hx

end SuperAut

end VOA
