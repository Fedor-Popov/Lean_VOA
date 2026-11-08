/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessSign
import VOA.Moonshine.MonsterGriess.SpinMatrixLaws
import VOA.Moonshine.TFormAlg
import VOA.Moonshine.CyclicTwisted

/-!
# Axiom's spin module `ℂ^SpinIdx` is the extraspecial module `T` of `V♮`

The twisted sector of `V♮` is `S[θ] ⊗ T` with `T = TLeechT` the simple module of the twisted group
algebra `A_Λ = alg (cocMat leech)` (`ExtraspecialModule.lean`; `e_α e_β = ε(α,β) e_{α+β}`, `T`
defined abstractly through Wedderburn–Artin).  Axiom's Griess algebra realises its `W`-block on
`ℚ^SpinIdx ⊗ ℚ²⁴` through the signed permutation matrices `qmatR` of `2^{1+24}`.  This file proves
that `ℂ^SpinIdx`, with `e_α` acting by the phased spin matrices
`spinOp p = Z(p) · qmatR 0 p.1 p.2` (`Z = signRefinement`, `p` the Axiom coordinates of `α`), is an
`A_Λ`-module isomorphic to `T`:

* `spinOp_mul` — `spinOp p · spinOp q = (−1)^{E(p,q)} spinOp (p + q)`: the product law of `qmatR`
  contributes `(−1)^{τ(p,q)}` (`qmatR_mul`), and the sign refinement converts `τ` into our cocycle
  exponent `E` (`signRefinement_add`, `B = E + τ`);
* `latRedEquiv` — Axiom's coordinates `C × Cocode ≅ (ZMod 2)^{rank}` (our `Λ/2Λ` in the canonical
  basis), `coordOfRed` its inverse;
* `spinAlgHom : A_Λ →ₐ[ℂ] End_ℂ(ℂ^SpinIdx)`, `e_x ↦ spinOp (coordOfRed x)`; it is injective (`A_Λ`
  is simple) and, by dimensions (`2^{24} = 4096²`), surjective;
* hence `ℂ^SpinIdx` is a simple `A_Λ`-module (`isSimpleModule_spinRep`), and by uniqueness of the
  simple module (`nonempty_linearEquiv_rep`) there is an `A_Λ`-linear isomorphism
  `spinIso : SpinRep ≃ₗ[A_Λ] TLeechT` with ⭐ `spinIso_spinOp`:
  `Ψ(spinOp(α) v) = eT α (Ψ v)` for every lattice vector `α`.

This is the `T`-factor of the twisted block of the Griess dictionary: `(T⁺)₂ = h(−½) ⊗ T` is to be
matched with `SpaceW = ℚ^{SpinIdx × 24}` through `Ψ ⊗ π`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.IntegralLattice VOA.LatGen VOA.Moonshine.AutMonster
open VOA.Moonshine.Extraspecial (alg op op_mem algBasis algBasis_mul algBasis_zero coe_algBasis
  coc)
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch (leechEquiv)
open Matrix

/-! ## §1  Axiom's coordinates of `Λ/2Λ` against the reduction of our lattice -/

theorem axiomRed_injective : Function.Injective axiomRed := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [axiomRed_mk] at hx
  obtain ⟨γ, hγ⟩ := (red_eq_zero_iff leech _).1 hx
  rw [Submodule.Quotient.mk_eq_zero, mem_two_range_iff]
  refine ⟨leechEquiv γ, ?_⟩
  have hu : u = leechEquiv (2 • γ) := by rw [← hγ, AddEquiv.apply_symm_apply]
  rw [hu, map_nsmul, two_nsmul, two_smul]
  rfl

theorem latRedLin_injective : Function.Injective latRedLin := fun p q h =>
  SpinLattice.phi0_injective (axiomRed_injective (by rw [← latRedLin_apply, ← latRedLin_apply]; exact h))

theorem latRedLin_surjective : Function.Surjective latRedLin := by
  intro x
  obtain ⟨α, rfl⟩ := red_surjective leech x
  refine ⟨SpinLattice.phi0Equiv.symm (Submodule.Quotient.mk (leechEquiv α)), ?_⟩
  rw [latRedLin_apply, ← SpinLattice.phi0Equiv_apply, LinearEquiv.apply_symm_apply, axiomRed_mk,
    AddEquiv.symm_apply_apply]

/-- **Axiom's coordinates of `Λ/2Λ` against ours**: `C × Cocode ≃ (ZMod 2)^{rank}`, `p ↦ red α` for
`α` in the class `phi0 p`. -/
noncomputable def latRedEquiv :
    (MonsterGriess.Code.C × Cocode) ≃ₗ[ZMod 2] (Fin leech.bRank → ZMod 2) :=
  LinearEquiv.ofBijective latRedLin ⟨latRedLin_injective, latRedLin_surjective⟩

/-- The Axiom coordinates of a class of `(ZMod 2)^{rank}`. -/
noncomputable def coordOfRed (x : Fin leech.bRank → ZMod 2) : MonsterGriess.Code.C × Cocode :=
  latRedEquiv.symm x

theorem latRedLin_coordOfRed (x : Fin leech.bRank → ZMod 2) : latRedLin (coordOfRed x) = x :=
  latRedEquiv.apply_symm_apply x

theorem coordOfRed_add (x y : Fin leech.bRank → ZMod 2) :
    coordOfRed (x + y) = coordOfRed x + coordOfRed y := map_add _ _ _

theorem coordOfRed_zero : coordOfRed 0 = 0 := map_zero _

/-- `E(coordOfRed x, coordOfRed y) = x ⬝ (cocMat · y)`. -/
theorem cocycleExp_coordOfRed (x y : Fin leech.bRank → ZMod 2) :
    cocycleExp (coordOfRed x) (coordOfRed y) = x ⬝ᵥ (cocMat leech *ᵥ y) := by
  rw [cocycleExp, latRedLin_coordOfRed, latRedLin_coordOfRed]

/-! ## §2  The phased spin matrices -/

theorem sgnR_eq_sgn (t : ZMod 2) : sgnR ℂ t = Extraspecial.sgn t := by
  rcases zmod_two_cases t with rfl | rfl
  · rw [sgnR_zero, Extraspecial.sgn_zero]
  · rw [sgnR_one, Extraspecial.sgn_one]

/-- **The phased spin matrix** of an Axiom coordinate: `spinOp p = Z(p) · qmatR 0 p.1 p.2`. -/
noncomputable def spinOp (p : MonsterGriess.Code.C × Cocode) : Matrix SpinIdx SpinIdx ℂ :=
  signRefinement p • qmatR ℂ 0 p.1 p.2

/-- ⭐ **The spin matrices satisfy our cocycle relations**:
`spinOp p · spinOp q = (−1)^{E(p,q)} spinOp (p + q)`. -/
theorem spinOp_mul (p q : MonsterGriess.Code.C × Cocode) :
    spinOp p * spinOp q = Extraspecial.sgn (cocycleExp p q) • spinOp (p + q) := by
  have h0 : (0 : ZMod 2) + 0 + pair q.1 p.2 = pair q.1 p.2 + 0 := by ring
  rw [spinOp, spinOp, spinOp, Matrix.smul_mul, Matrix.mul_smul, qmatR_mul, h0,
    ← sgnR_smul_qmatR, smul_smul, smul_smul, smul_smul, signRefinement_add, signForm_apply,
    Extraspecial.sgn_add, sgnR_eq_sgn, Prod.fst_add, Prod.snd_add]
  congr 1
  have hs := Extraspecial.sgn_mul_self (cocycleExp p q)
  linear_combination
    (-(signRefinement p * signRefinement q * Extraspecial.sgn (pair q.1 p.2))) * hs

theorem spinOp_zero : spinOp 0 = 1 := by
  rw [spinOp, signRefinement_zero, one_smul]
  exact qmatR_zero

/-- On classes of our lattice: `spinOp(ᾱ) · spinOp(β̄) = ε(α,β) spinOp(α + β)`. -/
theorem spinOp_red_mul (α β : leech.carrier) :
    spinOp (coordOfRed (red leech α)) * spinOp (coordOfRed (red leech β))
      = latticeCocycle leech α β • spinOp (coordOfRed (red leech (α + β))) := by
  rw [spinOp_mul, cocycleExp_coordOfRed, map_add, coordOfRed_add, latticeCocycle_eq_coc]
  rfl

/-! ## §3  The algebra homomorphism `A_Λ → End(ℂ^SpinIdx)` -/

/-- The linear map `e_x ↦ spinOp (coordOfRed x)` on the basis of `A_Λ`. -/
noncomputable def spinAlgLin :
    alg (cocMat leech) →ₗ[ℂ] Module.End ℂ (SpinIdx → ℂ) :=
  (algBasis (cocMat leech)).constr ℂ fun x => Matrix.toLinAlgEquiv' (spinOp (coordOfRed x))

theorem spinAlgLin_basis (x : Fin leech.bRank → ZMod 2) :
    spinAlgLin (algBasis (cocMat leech) x) = Matrix.toLinAlgEquiv' (spinOp (coordOfRed x)) := by
  rw [spinAlgLin, Module.Basis.constr_basis]

theorem spinAlgLin_one : spinAlgLin 1 = 1 := by
  rw [← algBasis_zero, spinAlgLin_basis, coordOfRed_zero, spinOp_zero, map_one]

theorem spinAlgLin_mul (a b : alg (cocMat leech)) :
    spinAlgLin (a * b) = spinAlgLin a * spinAlgLin b := by
  let f : alg (cocMat leech) →ₗ[ℂ] alg (cocMat leech) →ₗ[ℂ] Module.End ℂ (SpinIdx → ℂ) :=
    (LinearMap.mul ℂ (alg (cocMat leech))).compr₂ spinAlgLin
  let g : alg (cocMat leech) →ₗ[ℂ] alg (cocMat leech) →ₗ[ℂ] Module.End ℂ (SpinIdx → ℂ) :=
    (LinearMap.mul ℂ (Module.End ℂ (SpinIdx → ℂ))).compl₁₂ spinAlgLin spinAlgLin
  have hfg : f = g := by
    refine (algBasis (cocMat leech)).ext fun x => (algBasis (cocMat leech)).ext fun y => ?_
    simp only [f, g, LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₁₂_apply]
    rw [algBasis_mul, map_smul, spinAlgLin_basis, spinAlgLin_basis, spinAlgLin_basis, ← map_mul,
      spinOp_mul, cocycleExp_coordOfRed, ← coordOfRed_add, map_smul]
    rfl
  exact congrArg (fun F : alg (cocMat leech) →ₗ[ℂ] alg (cocMat leech) →ₗ[ℂ]
    Module.End ℂ (SpinIdx → ℂ) => F a b) hfg

/-- **The spin representation of `A_Λ`**: `e_x ↦ spinOp (coordOfRed x)`. -/
noncomputable def spinAlgHom : alg (cocMat leech) →ₐ[ℂ] Module.End ℂ (SpinIdx → ℂ) :=
  AlgHom.ofLinearMap spinAlgLin spinAlgLin_one spinAlgLin_mul

theorem spinAlgHom_algBasis (x : Fin leech.bRank → ZMod 2) :
    spinAlgHom (algBasis (cocMat leech) x) = Matrix.toLinAlgEquiv' (spinOp (coordOfRed x)) :=
  spinAlgLin_basis x

theorem spinAlgHom_eA (α : leech.carrier) :
    spinAlgHom (eA leech α) = Matrix.toLinAlgEquiv' (spinOp (coordOfRed (red leech α))) := by
  rw [← spinAlgHom_algBasis]
  congr 1
  apply Subtype.ext
  rw [coe_algBasis]
  rfl

theorem spinAlgHom_injective : Function.Injective spinAlgHom := by
  haveI := isSimpleRing_alg_cocMat leech leech_even leech_isUnit_det_gramMat
  exact RingHom.injective (spinAlgHom : alg (cocMat leech) →+* Module.End ℂ (SpinIdx → ℂ))

theorem finrank_C₀ : Module.finrank (ZMod 2) C₀ = 11 := by
  have h := LinearMap.finrank_range_add_finrank_ker μ₀
  have hr : LinearMap.range μ₀ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    exact ⟨t • ΩC, by rw [map_smul, μ₀_ΩC, smul_eq_mul, mul_one]⟩
  rw [hr, finrank_top, Module.finrank_self, MonsterGriess.Code.finrank_C] at h
  change Module.finrank (ZMod 2) (LinearMap.ker μ₀) = 11
  omega

theorem card_spinIdx : Fintype.card SpinIdx = 4096 := by
  rw [Fintype.card_prod, ZMod.card]
  have h : Fintype.card C₀ = 2 ^ 11 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := C₀), ZMod.card, finrank_C₀]
  rw [h]
  norm_num

theorem spinAlgHom_surjective : Function.Surjective spinAlgHom := by
  have hdim : Module.finrank ℂ (alg (cocMat leech)) = Module.finrank ℂ (Module.End ℂ (SpinIdx → ℂ)) := by
    rw [finrank_alg_cocMat, leech_rank, Module.finrank_linearMap,
      Module.finrank_fintype_fun_eq_card, card_spinIdx]
    norm_num
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := spinAlgHom.toLinearMap)).1 spinAlgHom_injective

/-! ## §4  `ℂ^SpinIdx` as an `A_Λ`-module, and the isomorphism with `T` -/

/-- `ℂ^SpinIdx`, as a carrier for the `A_Λ`-module structure. -/
def SpinRep : Type := SpinIdx → ℂ

noncomputable instance : AddCommGroup SpinRep := inferInstanceAs (AddCommGroup (SpinIdx → ℂ))

noncomputable instance : Module ℂ SpinRep := inferInstanceAs (Module ℂ (SpinIdx → ℂ))

noncomputable instance : Module (Module.End ℂ (SpinIdx → ℂ)) SpinRep :=
  inferInstanceAs (Module (Module.End ℂ (SpinIdx → ℂ)) (SpinIdx → ℂ))

noncomputable instance : Module (alg (cocMat leech)) SpinRep :=
  Module.compHom SpinRep
    (spinAlgHom : alg (cocMat leech) →+* Module.End ℂ (SpinIdx → ℂ))

theorem spinRep_smul_def (a : alg (cocMat leech)) (v : SpinRep) :
    a • v = (spinAlgHom a : Module.End ℂ (SpinIdx → ℂ)) v := rfl

instance : IsScalarTower ℂ (alg (cocMat leech)) SpinRep where
  smul_assoc c a v := by
    change (spinAlgHom (c • a) : Module.End ℂ (SpinIdx → ℂ)) v = c • (spinAlgHom a : Module.End ℂ (SpinIdx → ℂ)) v
    rw [map_smul, LinearMap.smul_apply]

instance : Nontrivial SpinRep := inferInstanceAs (Nontrivial (SpinIdx → ℂ))

/-- **`ℂ^SpinIdx` is a simple `A_Λ`-module** (the spin representation is onto `End`). -/
instance isSimpleModule_spinRep : IsSimpleModule (alg (cocMat leech)) SpinRep := by
  have hE := (isSimpleModule_iff_toSpanSingleton_surjective
    (R := Module.End ℂ (SpinIdx → ℂ)) (M := SpinIdx → ℂ)).mp inferInstance
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, fun x hx y => ?_⟩
  obtain ⟨f, hf⟩ := hE.2 x hx y
  obtain ⟨a, rfl⟩ := spinAlgHom_surjective f
  refine ⟨a, ?_⟩
  simp only [LinearMap.toSpanSingleton_apply] at hf ⊢
  rw [spinRep_smul_def]
  exact hf

/-- ⭐ **The spin module is `T`**: an `A_Λ`-linear isomorphism `ℂ^SpinIdx ≃ TLeechT` (unique up to a
scalar, by Schur). -/
noncomputable def spinIso : SpinRep ≃ₗ[alg (cocMat leech)] TLeechT :=
  Classical.choice (Extraspecial.nonempty_linearEquiv_rep (cocMat leech)
    (isUnit_det_cocMat leech leech_even leech_isUnit_det_gramMat) SpinRep)

/-- ⭐ **`Ψ` intertwines the spin matrices with `T`**: `Ψ(spinOp(ᾱ) v) = e_α (Ψ v)` for every
vector `α` of our Leech lattice. -/
theorem spinIso_spinOp (α : leech.carrier) (v : SpinRep) :
    spinIso ((spinOp (coordOfRed (red leech α))).mulVec v : SpinIdx → ℂ)
      = eT leech leech_even leech_isUnit_det_gramMat α (spinIso v) := by
  have h := spinIso.map_smul (eA leech α) v
  rw [spinRep_smul_def, spinAlgHom_eA, Matrix.toLinAlgEquiv'_apply] at h
  rw [IntegralLattice.eT_apply]
  exact h

end VOA.Moonshine.GriessDictionary
