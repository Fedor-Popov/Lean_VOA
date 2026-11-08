/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessSpinDict
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# The Griess algebra of `V♮` is Axiom's rational Griess algebra, tensored with `ℂ`

This file assembles the Griess dictionary

  `griessNat : SpaceB → V♮₂`,   `(A, x, N) ↦ (Q_C(A^π) + Σ_c x_c ζ'_c x_{α_c},  λ Σᵢ h_{fᵢ}(−½) ⊗ Ψ(N_{·πi}))`

(untwisted block: `MoonshineCNGriessUntwisted` with the phases `ζ' = fullShortSign`; twisted block:
`spinDict`, `MoonshineCNGriessSpinDict`) and proves that it is an isomorphism of algebras with
forms after extension of scalars to `ℂ`.

* **`W·W` channel** (`vnat_smul_spinDict_spinDict`): the product of two twisted states is
  identified through the form.  Twisted × twisted lands in `V_Λ⁺`; its pairing with `untwistedDict u`
  is, by FHL invariance (`natForm_smul_one_adjoint`) and commutativity, the pairing of a twisted
  state with the `A·W`/`X·W` image, which Axiom's invariance `bform_gmul_spinBlock_spinBlock` turns
  into `2·bform (N·M) u`; the untwisted dictionary images of a `ℚ`-basis span `(V_Λ⁺)₂`
  (`span_fullUntwistedImage`), so the pairing determines the product.
* ⭐ `griessNat_gmul`, ⭐ `griessNat_form` — multiplicativity and `natForm = 2·bform`, for all
  `u, v ∈ SpaceB`, with no hypothesis.
* ⭐ `griessIso : ℂ ⊗[ℚ] SpaceB ≃ₗ[ℂ] VnatVOA.grading 2`, `griessIso_tmul` (`1 ⊗ u ↦ griessNat u`),
  ⭐ `griessIso_mul` (the base change of `gmul` goes to the Griess product of `V♮`),
  ⭐ `griessIso_form` (`natForm = 2 · bform_ℂ`).
* Block statements: `griessIso_tmul_spinBlock` (`W` goes to `0 × (T⁺)₂`), `span_range_spinDict`
  (the `W`-images span `(T⁺)₂`), `griessIso_tmul_untwisted`, and the frame halves
  `spinDict_mem_TPframe` (rows of `SpaceW` in the half `C₀ × {t}` go to the frame sector
  `T_s⁺` with `(−1)^s = κ_J (−1)^t`, `κ_J = frameSign`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop
open VOA.LatGen VOA.IntegralLattice
open VOA.Moonshine.InvForm
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch (piPerm)
open Matrix
open scoped TensorProduct

/-! ## §1  Axiom's side: symmetry of `bform`, the untwisted part, block products -/

theorem bform_symm (u v : SpaceB) : bform u v = bform v u := by
  rw [bform_apply, bform_apply, trace_mul_comm]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem bform_nondegenerate : bform.Nondegenerate :=
  ⟨fun u hu => bform_self_eq_zero (hu u), fun u hu => bform_self_eq_zero (hu u)⟩

/-- The untwisted part `(A, x, 0)` of `u = (A, x, N)`. -/
def untwistedPart (u : SpaceB) : SpaceB := (u.1, u.2.1, 0)

theorem untwistedPart_snd_snd (u : SpaceB) : (untwistedPart u).2.2 = 0 := rfl

theorem eq_untwistedPart_add (u : SpaceB) : u = untwistedPart u + spinBlock u.2.2 := by
  obtain ⟨A, x, N⟩ := u
  simp [untwistedPart, spinBlock]

theorem untwistedDict_untwistedPart (ζ : ShortIdx → ℂ) (u : SpaceB) :
    untwistedDict ζ (untwistedPart u) = untwistedDict ζ u := rfl

theorem spinBlockAction_untwistedPart (u : SpaceB) (N : SpaceW) :
    spinBlockAction (untwistedPart u) N = spinBlockAction u N := rfl

theorem spinBlock_snd_snd (N : SpaceW) : (spinBlock N).2.2 = N := rfl

theorem untwistedDict_spinBlock (ζ : ShortIdx → ℂ) (N : SpaceW) :
    untwistedDict ζ (spinBlock N) = 0 := by
  rw [untwistedDict_apply]
  change matDict ((0 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) + shortDict ζ 0 = 0
  rw [Submodule.coe_zero, map_zero, map_zero, add_zero]

/-- The product of two untwisted vectors has no `W`-part. -/
theorem gmul_snd_snd_of_untwisted {u v : SpaceB} (hu : u.2.2 = 0) (hv : v.2.2 = 0) :
    (gmul u v).2.2 = 0 := by
  rw [gmul_snd_snd]
  simp [gmulW, gmulWHalf, Nm, hu, hv]

/-- The decomposition of `u·v` into its four block products. -/
theorem gmul_eq_blocks (u v : SpaceB) :
    gmul u v = gmul (untwistedPart u) (untwistedPart v) + spinBlock (spinBlockAction u v.2.2)
      + spinBlock (spinBlockAction v u.2.2) + gmul (spinBlock u.2.2) (spinBlock v.2.2) := by
  conv_lhs => rw [eq_untwistedPart_add u, eq_untwistedPart_add v]
  simp only [map_add, LinearMap.add_apply]
  rw [gmul_untwisted_spinBlock (untwistedPart_snd_snd u),
    gmul_spinBlock_untwisted (untwistedPart_snd_snd v), spinBlockAction_untwistedPart,
    spinBlockAction_untwistedPart]
  abel

theorem bform_eq_untwistedPart_add (u v : SpaceB) :
    bform u v = bform (untwistedPart u) (untwistedPart v) + ∑ j, ∑ i, u.2.2 j i * v.2.2 j i := by
  simp only [bform_apply, untwistedPart, Matrix.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero]

/-! ## §2  The untwisted images with the phases `ζ'` span `(V_Λ⁺)₂` -/

/-- The untwisted dictionary images (phases `ζ'`) of a `ℚ`-basis of `U`. -/
noncomputable def fullUntwistedImage (k : Fin (Module.finrank ℚ untwistedSub)) : VPlus :=
  untwistedDict fullShortSign (untwistedBasisQ k : SpaceB)

theorem plusForm_dual_fullUntwistedImage (l k : Fin (Module.finrank ℚ untwistedSub)) :
    plusForm (untwistedDict fullShortSign
        ((bform.restrict untwistedSub).dualBasis bform_restrict_nondegenerate untwistedBasisQ l : SpaceB))
      (fullUntwistedImage k) = 2 * ((if k = l then 1 else 0 : ℚ) : ℂ) := by
  rw [fullUntwistedImage, untwistedDict_form shortSignDictionary_fullShortSign
    (mem_untwistedSub.1 ((bform.restrict untwistedSub).dualBasis bform_restrict_nondegenerate
      untwistedBasisQ l).2) (mem_untwistedSub.1 (untwistedBasisQ k).2)]
  have := LinearMap.BilinForm.apply_dualBasis_left bform_restrict_nondegenerate untwistedBasisQ l k
  rw [bform_restrict_apply] at this
  rw [this]

theorem linearIndependent_fullUntwistedImage : LinearIndependent ℂ fullUntwistedImage := by
  classical
  rw [linearIndependent_iff']
  intro s g hg l hl
  have h := congrArg (fun y => plusForm (untwistedDict fullShortSign
    ((bform.restrict untwistedSub).dualBasis bform_restrict_nondegenerate untwistedBasisQ l : SpaceB)) y) hg
  simp only [map_sum, map_smul, map_zero, smul_eq_mul, plusForm_dual_fullUntwistedImage] at h
  rw [Finset.sum_eq_single l (fun k _ hkl => by rw [if_neg hkl]; simp)
    (fun h' => absurd hl h')] at h
  rw [if_pos rfl] at h
  simpa using h

theorem span_fullUntwistedImage :
    Submodule.span ℂ (Set.range fullUntwistedImage) = leechVOAPlus.grading 2 := by
  haveI : FiniteDimensional ℂ (leechVOAPlus.grading 2) := leechVOAPlus.finrank 2
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact untwistedDict_mem_grading_two _
  · rw [finrank_span_eq_card linearIndependent_fullUntwistedImage, Fintype.card_fin,
      finrank_leechPlus_two]

/-- **`plusForm` separates `(V_Λ⁺)₂` against the dictionary**: a vector of `(V_Λ⁺)₂` orthogonal to every
`untwistedDict ζ' u` vanishes. -/
theorem eq_zero_of_plusForm_untwistedDict {y : VPlus} (hy : y ∈ leechVOAPlus.grading 2)
    (h : ∀ u : SpaceB, u.2.2 = 0 → plusForm (untwistedDict fullShortSign u) y = 0) : y = 0 := by
  classical
  rw [← span_fullUntwistedImage] at hy
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hy
  have hc : ∀ l, c l = 0 := by
    intro l
    have h0 := h _ (mem_untwistedSub.1 ((bform.restrict untwistedSub).dualBasis
      bform_restrict_nondegenerate untwistedBasisQ l).2)
    simp only [map_sum, map_smul, smul_eq_mul, plusForm_dual_fullUntwistedImage] at h0
    rw [Finset.sum_eq_single l (fun k _ hkl => by rw [if_neg hkl]; simp)
      (fun h' => absurd (Finset.mem_univ l) h')] at h0
    rw [if_pos rfl] at h0
    simpa using h0
  simp [hc]

/-! ## §3  The `W·W` channel -/

theorem spinDict_pair_mem (N : SpaceW) : (((0 : VPlus), spinDict N) : Vnat) ∈ gradingNat 2 :=
  mem_gradingNat.2 ⟨Submodule.zero_mem _, spinDict_mem_weight_two N⟩

theorem untwistedDict_pair_mem (u : SpaceB) :
    ((untwistedDict fullShortSign u, (0 : TP)) : Vnat) ∈ gradingNat 2 :=
  mem_gradingNat.2 ⟨untwistedDict_mem_grading_two _, Submodule.zero_mem _⟩

/-- ⭐ **The `W·W` channel**: `(0, spinDict N)₍₁₎(0, spinDict M) = (untwistedDict ζ' (N·M), 0)`. -/
theorem vnat_smul_spinDict_spinDict (N M : SpaceW) :
    VnatVOA.smul ((0, spinDict N) : Vnat) 1 ((0, spinDict M) : Vnat)
      = (untwistedDict fullShortSign (gmul (spinBlock N) (spinBlock M)), 0) := by
  set P := VnatVOA.smul ((0, spinDict N) : Vnat) 1 ((0, spinDict M) : Vnat) with hP
  have hP2 : P.2 = 0 := vnat_smul_twisted_twisted_snd _ _ 1
  have hPmem : P ∈ gradingNat 2 := by
    have hx : ((0, spinDict N) : Vnat) ∈ VnatVOA.grading 2 := by
      rw [VnatVOA_grading]; exact spinDict_pair_mem N
    have hy : ((0, spinDict M) : Vnat) ∈ VnatVOA.grading 2 := by
      rw [VnatVOA_grading]; exact spinDict_pair_mem M
    have := VnatVOA.smul_mem_grading hx hy 1
    rw [show (2 : ℤ) + 2 - 1 - 1 = 2 by norm_num, VnatVOA_grading] at this
    exact this
  have hdiff : P.1 - untwistedDict fullShortSign (gmul (spinBlock N) (spinBlock M)) = 0 := by
    refine eq_zero_of_plusForm_untwistedDict
      (Submodule.sub_mem _ (mem_gradingNat.1 hPmem).1 (untwistedDict_mem_grading_two _)) ?_
    intro u hu
    have hnat : SimpleNat.natForm ((untwistedDict fullShortSign u, 0) : Vnat) P
        = plusForm (untwistedDict fullShortSign u) P.1 := by
      rw [SimpleNat.natForm_apply]
      show leechBV (untwistedDict fullShortSign u) P.1 + TPForm (0 : TP) P.2 = _
      rw [map_zero, LinearMap.zero_apply, add_zero, leechBV_eq_plusForm]
    have e1 : plusForm (untwistedDict fullShortSign u) P.1
        = 2 * (bform (gmul (spinBlock N) (spinBlock M)) u : ℂ) := by
      rw [← hnat, SimpleNat.natForm_symm, hP, natForm_smul_one_adjoint (spinDict_pair_mem N),
        vnat_smul_one_comm (spinDict_pair_mem N) (untwistedDict_pair_mem u),
        vnat_smul_untwisted_twisted, SimpleNat.natForm_apply]
      dsimp only
      rw [topAct_untwistedDict_spinDict, TPForm_spinDict, bform_gmul_spinBlock_spinBlock N M hu,
        bform_spinBlock_spinBlock]
      simp
    have e2 : plusForm (untwistedDict fullShortSign u)
        (untwistedDict fullShortSign (gmul (spinBlock N) (spinBlock M)))
        = 2 * (bform (gmul (spinBlock N) (spinBlock M)) u : ℂ) := by
      rw [untwistedDict_form shortSignDictionary_fullShortSign hu
        (gmul_spinBlock_spinBlock_snd_snd N M), bform_symm]
    rw [map_sub, e1, e2, sub_self]
  exact Prod.ext (sub_eq_zero.1 hdiff) hP2

/-! ## §4  The full rational dictionary -/

theorem griessNat_mem (u : SpaceB) :
    ((untwistedDict fullShortSign u, spinDict u.2.2) : Vnat) ∈ VnatVOA.grading 2 := by
  rw [VnatVOA_grading, mem_gradingNat]
  exact ⟨untwistedDict_mem_grading_two _, spinDict_mem_weight_two _⟩

/-- ⭐ **The full rational Griess dictionary** `SpaceB → V♮₂`:
`(A, x, N) ↦ (Q_C(A^π) + Σ_c x_c ζ'_c x_{α_c}, λ Σᵢ h_{fᵢ}(−½) ⊗ Ψ(N_{·πi}))`. -/
noncomputable def griessNat : SpaceB →+ VnatVOA.grading 2 where
  toFun u := ⟨(untwistedDict fullShortSign u, spinDict u.2.2), griessNat_mem u⟩
  map_zero' := by
    apply Subtype.ext
    change ((untwistedDict fullShortSign 0, spinDict (0 : SpaceW)) : Vnat) = 0
    rw [map_zero, map_zero]
    rfl
  map_add' u v := by
    apply Subtype.ext
    change ((untwistedDict fullShortSign (u + v), spinDict (u.2.2 + v.2.2)) : Vnat) = _
    rw [map_add, map_add]
    rfl

theorem griessNat_coe (u : SpaceB) :
    (griessNat u : Vnat) = (untwistedDict fullShortSign u, spinDict u.2.2) := rfl

theorem griessNat_smul (q : ℚ) (u : SpaceB) : griessNat (q • u) = (q : ℂ) • griessNat u := by
  apply Subtype.ext
  rw [Submodule.coe_smul, griessNat_coe, griessNat_coe]
  change ((untwistedDict fullShortSign (q • u), spinDict (q • u.2.2)) : Vnat) = _
  rw [untwistedDict_smul, spinDict_smul]
  rfl

theorem griessNat_coe_split (u : SpaceB) :
    (griessNat u : Vnat) = ((untwistedDict fullShortSign (untwistedPart u), 0) : Vnat)
      + ((0, spinDict u.2.2) : Vnat) := by
  rw [griessNat_coe, untwistedDict_untwistedPart]
  refine Prod.ext ?_ ?_ <;> simp

/-- ⭐ **The Griess dictionary is multiplicative**: `griessNat (u·v) = griessNat u × griessNat v`
(Griess product of `VnatVOA`), for all `u, v ∈ SpaceB`. -/
theorem griessNat_gmul (u v : SpaceB) :
    griessNat (gmul u v) = VnatVOA.griessMul (griessNat u) (griessNat v) := by
  apply Subtype.ext
  rw [VertexOperatorAlgebra.griessMul_coe, griessNat_coe_split u, griessNat_coe_split v]
  simp only [PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right]
  rw [vnat_smul_untwisted, ← untwistedDict_gmul shortSignDictionary_fullShortSign
      (untwistedPart_snd_snd u) (untwistedPart_snd_snd v),
    vnat_smul_untwisted_twisted, topAct_untwistedDict_spinDict,
    vnat_smul_one_comm (spinDict_pair_mem u.2.2) (untwistedDict_pair_mem (untwistedPart v)),
    vnat_smul_untwisted_twisted, topAct_untwistedDict_spinDict, vnat_smul_spinDict_spinDict,
    spinBlockAction_untwistedPart, spinBlockAction_untwistedPart, griessNat_coe, gmul_eq_blocks u v]
  refine Prod.ext ?_ ?_
  · simp only [map_add, untwistedDict_spinBlock, Prod.fst_add, add_zero, zero_add]
  · simp only [Prod.snd_add, gmul_snd_snd_of_untwisted (untwistedPart_snd_snd u)
      (untwistedPart_snd_snd v), gmul_spinBlock_spinBlock_snd_snd, spinBlock_snd_snd, map_add,
      zero_add, add_zero]
    exact add_comm _ _

/-- ⭐ **The Griess dictionary is an isometry up to `2`**: `natForm (griessNat u) (griessNat v) =
2·bform u v`, for all `u, v ∈ SpaceB`. -/
theorem griessNat_form (u v : SpaceB) :
    SimpleNat.natForm (griessNat u : Vnat) (griessNat v : Vnat) = 2 * (bform u v : ℂ) := by
  rw [griessNat_coe, griessNat_coe, SimpleNat.natForm_apply, leechBV_eq_plusForm]
  change plusForm (untwistedDict fullShortSign (untwistedPart u))
      (untwistedDict fullShortSign (untwistedPart v)) + TPForm (spinDict u.2.2) (spinDict v.2.2) = _
  rw [untwistedDict_form shortSignDictionary_fullShortSign (untwistedPart_snd_snd u)
    (untwistedPart_snd_snd v), TPForm_spinDict, bform_eq_untwistedPart_add u v]
  push_cast
  ring

/-! ## §5  The `ℂ`-linear isomorphism -/

/-- A `ℚ`-basis of `SpaceB`. -/
noncomputable def griessBasisQ : Module.Basis (Fin (Module.finrank ℚ SpaceB)) ℚ SpaceB :=
  Module.finBasis ℚ SpaceB

/-- The images in `V♮` of the `ℚ`-basis vectors. -/
noncomputable def griessImage (k : Fin (Module.finrank ℚ SpaceB)) : Vnat :=
  (griessNat (griessBasisQ k) : Vnat)

theorem natForm_dual_griessImage (l k : Fin (Module.finrank ℚ SpaceB)) :
    SimpleNat.natForm (griessNat (bform.dualBasis bform_nondegenerate griessBasisQ l) : Vnat)
      (griessImage k) = 2 * ((if k = l then 1 else 0 : ℚ) : ℂ) := by
  rw [griessImage, griessNat_form, LinearMap.BilinForm.apply_dualBasis_left]

/-- **The images of a `ℚ`-basis are `ℂ`-linearly independent** (isometry and positivity of `bform`). -/
theorem linearIndependent_griessImage : LinearIndependent ℂ griessImage := by
  classical
  rw [linearIndependent_iff']
  intro s g hg l hl
  have h := congrArg (fun y => SimpleNat.natForm
    (griessNat (bform.dualBasis bform_nondegenerate griessBasisQ l) : Vnat) y) hg
  simp only [map_sum, map_smul, map_zero, smul_eq_mul, natForm_dual_griessImage] at h
  rw [Finset.sum_eq_single l (fun k _ hkl => by rw [if_neg hkl]; simp)
    (fun h' => absurd hl h')] at h
  rw [if_pos rfl] at h
  simpa using h

/-- `dim_ℚ SpaceB = dim_ℂ V♮₂`. -/
theorem finrank_spaceB : Module.finrank ℚ SpaceB = Module.finrank ℂ (VnatVOA.grading 2) := by
  set p : SpaceB →ₗ[ℚ] SpaceW :=
    (LinearMap.snd ℚ SpaceX SpaceW).comp (LinearMap.snd ℚ symMat (SpaceX × SpaceW)) with hp
  have hsurj : LinearMap.range p = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro N
    exact ⟨spinBlock N, rfl⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [hsurj, finrank_top] at hrn
  change Module.finrank ℚ SpaceW + Module.finrank ℚ untwistedSub = _ at hrn
  rw [← hrn, VnatVOA_grading, finrank_gradingNat, finrank_leechPlus_two,
    show (((2 : ℤ) : ℂ)) = (2 : ℂ) by norm_num, finrank_plusModule_weight_two,
    Module.finrank_matrix, Module.finrank_self, card_spinIdx, Fintype.card_fin]
  ring

/-- **A `ℂ`-basis of `V♮₂`**: the dictionary images of a `ℚ`-basis of `SpaceB`. -/
noncomputable def griessBasisC :
    Module.Basis (Fin (Module.finrank ℚ SpaceB)) ℂ (VnatVOA.grading 2) :=
  haveI : FiniteDimensional ℂ (VnatVOA.grading 2) := VnatVOA.finrank 2
  basisOfLinearIndependentOfCardEqFinrank' (fun k => griessNat (griessBasisQ k))
    (LinearIndependent.of_comp (VnatVOA.grading 2).subtype linearIndependent_griessImage)
    (by rw [Fintype.card_fin, finrank_spaceB])

theorem griessBasisC_apply (k : Fin (Module.finrank ℚ SpaceB)) :
    griessBasisC k = griessNat (griessBasisQ k) := by
  simp [griessBasisC]

/-- ⭐ **The Griess algebra of `V♮` is Axiom's rational Griess algebra over `ℂ`**:
`ℂ ⊗[ℚ] SpaceB ≃ₗ[ℂ] V♮₂`, `1 ⊗ u ↦ griessNat u`. -/
noncomputable def griessIso : ℂ ⊗[ℚ] SpaceB ≃ₗ[ℂ] VnatVOA.grading 2 :=
  (Algebra.TensorProduct.basis ℂ griessBasisQ).equiv griessBasisC (Equiv.refl _)

/-- ⭐ **`griessIso` extends the rational dictionary**: `griessIso (1 ⊗ u) = griessNat u`. -/
theorem griessIso_tmul (u : SpaceB) : griessIso (1 ⊗ₜ u) = griessNat u := by
  have hsum : griessNat u = ∑ k, ((griessBasisQ.repr u k : ℚ) : ℂ) • griessNat (griessBasisQ k) := by
    conv_lhs => rw [← griessBasisQ.sum_repr u]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => griessNat_smul _ _
  conv_lhs => rw [← griessBasisQ.sum_repr u]
  rw [TensorProduct.tmul_sum, map_sum, hsum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ (griessBasisQ.repr u k), map_smul,
    ← Algebra.TensorProduct.basis_apply, griessIso, Module.Basis.equiv_apply, Equiv.refl_apply,
    griessBasisC_apply, eq_ratCast]

theorem griessIso_tmul_smul (a : ℂ) (u : SpaceB) : griessIso (a ⊗ₜ u) = a • griessNat u := by
  rw [show a ⊗ₜ[ℚ] u = a • ((1 : ℂ) ⊗ₜ[ℚ] u) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, griessIso_tmul]

theorem vnat_griessMul_smul_left (c : ℂ) (u v : VnatVOA.grading 2) :
    VnatVOA.griessMul (c • u) v = c • VnatVOA.griessMul u v := by
  apply Subtype.ext
  simp only [VertexOperatorAlgebra.griessMul_coe, Submodule.coe_smul,
    PreVertexAlgebra.smul_smul_left]

theorem vnat_griessMul_smul_right (c : ℂ) (u v : VnatVOA.grading 2) :
    VnatVOA.griessMul u (c • v) = c • VnatVOA.griessMul u v := by
  apply Subtype.ext
  simp only [VertexOperatorAlgebra.griessMul_coe, Submodule.coe_smul,
    PreVertexAlgebra.smul_smul_right]

theorem vnat_griessMul_zero_left (v : VnatVOA.grading 2) : VnatVOA.griessMul 0 v = 0 := by
  have h := vnat_griessMul_smul_left 0 0 v
  rwa [zero_smul, zero_smul] at h

theorem vnat_griessMul_zero_right (u : VnatVOA.grading 2) : VnatVOA.griessMul u 0 = 0 := by
  have h := vnat_griessMul_smul_right 0 u 0
  rwa [zero_smul, zero_smul] at h

/-- ⭐ **`griessIso` is an algebra isomorphism**: the base change of Axiom's product goes to the
Griess product of `V♮`. -/
theorem griessIso_mul (x y : ℂ ⊗[ℚ] SpaceB) :
    griessIso (LinearMap.BilinMap.baseChange ℂ gmul x y)
      = VnatVOA.griessMul (griessIso x) (griessIso y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, vnat_griessMul_zero_left]
  | add x x' hx hx' =>
      simp only [map_add, LinearMap.add_apply, hx, hx', VertexOperatorAlgebra.griessMul_add_left]
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, vnat_griessMul_zero_right]
      | add y y' hy hy' =>
          simp only [map_add, hy, hy', VertexOperatorAlgebra.griessMul_add_right]
      | tmul b v =>
          rw [LinearMap.BilinMap.baseChange_tmul, griessIso_tmul_smul, griessIso_tmul_smul,
            griessIso_tmul_smul, griessNat_gmul, vnat_griessMul_smul_left,
            vnat_griessMul_smul_right, smul_smul]

/-- ⭐ **`griessIso` is an isometry up to `2`**: `natForm (griessIso x) (griessIso y) =
2 · bform_ℂ x y`. -/
theorem griessIso_form (x y : ℂ ⊗[ℚ] SpaceB) :
    SimpleNat.natForm (griessIso x : Vnat) (griessIso y : Vnat)
      = 2 * LinearMap.BilinForm.baseChange ℂ bform x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' =>
      simp only [map_add, Submodule.coe_add, LinearMap.add_apply, hx, hx', mul_add]
  | tmul a u =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
          simp only [map_add, Submodule.coe_add, hy, hy', mul_add]
      | tmul b v =>
          rw [LinearMap.BilinForm.baseChange_tmul, griessIso_tmul_smul, griessIso_tmul_smul,
            Submodule.coe_smul, Submodule.coe_smul]
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
          rw [griessNat_form, Rat.smul_def]
          ring

/-! ## §6  Block statements -/

/-- ⭐ **`W` goes to the twisted block**: `griessIso (1 ⊗ (0,0,N)) = (0, spinDict N)`. -/
theorem griessIso_tmul_spinBlock (N : SpaceW) :
    (griessIso (1 ⊗ₜ spinBlock N) : Vnat) = (0, spinDict N) := by
  rw [griessIso_tmul, griessNat_coe, untwistedDict_spinBlock]
  rfl

/-- The untwisted part goes to `V_Λ⁺`: `griessIso (1 ⊗ u) = (untwistedDict ζ' u, 0)` for `u.2.2 = 0`. -/
theorem griessIso_tmul_untwisted {u : SpaceB} (hu : u.2.2 = 0) :
    (griessIso (1 ⊗ₜ u) : Vnat) = (untwistedDict fullShortSign u, 0) := by
  rw [griessIso_tmul, griessNat_coe, hu, map_zero]

theorem spinToConway_single (s : SpinIdx) (i : Fin 24) :
    spinToConway (Matrix.single s (piPerm i) (1 : ℚ)) = Matrix.single s i (1 : ℂ) := by
  ext s' i'
  rw [spinToConway_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases hs : s = s'
  · by_cases hi : i = i'
    · subst hs hi; simp
    · rw [if_neg (fun h => hi (piPerm.injective h.2)), if_neg (fun h => hi h.2)]
      simp
  · rw [if_neg (fun h => hs h.1), if_neg (fun h => hs h.1)]
    simp

theorem spinDictScale_ne_zero : spinDictScale ≠ 0 := by
  intro h
  have h2 := spinDictScale_sq
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, inv_eq_zero, mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · norm_num at h2
  · exact spinFormScale_ne_zero h2

theorem spinTopVec_injective : Function.Injective spinTopVec := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro N hN
  ext s i
  have h := TPForm_spinTopVec N (Matrix.single s i 1)
  rw [hN, map_zero, LinearMap.zero_apply] at h
  simp only [Matrix.single_apply, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_eq_single s (fun s' _ hs' => Finset.sum_eq_zero fun i' _ => by
      rw [if_neg (fun h' => hs' h'.1.symm)]) (by simp),
    Finset.sum_eq_single i (fun i' _ hi' => by rw [if_neg (fun h' => hi' h'.2.symm)]) (by simp),
    if_pos ⟨rfl, rfl⟩] at h
  have hκ := spinFormScale_ne_zero
  rw [Matrix.zero_apply]
  have : -4 * spinFormScale ≠ 0 := mul_ne_zero (by norm_num) hκ
  exact (mul_eq_zero.1 h.symm).resolve_left this

/-- ⭐ **The `W`-images span `(T⁺)₂`**. -/
theorem span_range_spinDict :
    Submodule.span ℂ (Set.range spinDict) = plusModule.weight (2 : ℂ) := by
  haveI : FiniteDimensional ℂ (plusModule.weight (2 : ℂ)) := plusModule.finrank 2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨N, rfl⟩
    exact spinDict_mem_weight_two N
  · have hrange : LinearMap.range spinTopVec = plusModule.weight (2 : ℂ) := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨N, rfl⟩
        exact spinTopVec_mem_weight_two N
      · rw [LinearMap.finrank_range_of_inj spinTopVec_injective, finrank_plusModule_weight_two,
          Module.finrank_matrix, Module.finrank_self, card_spinIdx, Fintype.card_fin]
    rw [← hrange]
    rintro _ ⟨N, rfl⟩
    rw [Matrix.matrix_eq_sum_single N, map_sum]
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [show Matrix.single s i (N s i) = N s i • Matrix.single s i (1 : ℂ) by
      rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul]
    refine Submodule.smul_mem _ _ ?_
    have h : spinTopVec (Matrix.single s i 1) = spinDictScale⁻¹ • spinDict (Matrix.single s (piPerm i) 1) := by
      rw [spinDict_apply, spinToConway_single, smul_smul, inv_mul_cancel₀ spinDictScale_ne_zero,
        one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- ⭐ **The frame halves**: a `W`-vector supported on the rows `C₀ × {t}` goes into the frame sector
`T_s⁺` with `(−1)^s = κ_J (−1)^t` (`κ_J = frameSign`, `κ_J² = 1`). -/
theorem spinDict_mem_TPframe {N : SpaceW} {t s : ZMod 2} (hN : ∀ j i, j.1 ≠ t → N j i = 0)
    (hs : Extraspecial.sgn s = frameSign * sgnR ℂ t) : spinDict N ∈ TPframe s := by
  have hterm : ∀ i : Fin 24,
      frameJL.lTensor (TwistedHeisenberg.FockT 24) ((spinTopState (conwayVec i) (fun j => spinToConway N j i) : TP) : Tw)
        = Extraspecial.sgn s • ((spinTopState (conwayVec i) (fun j => spinToConway N j i) : TP) : Tw) := by
    intro i
    have hcol : ∀ j : SpinIdx, j.1 ≠ t → ((fun j => spinToConway N j i) : SpinIdx → ℂ) j = 0 := by
      intro j hj
      change spinToConway N j i = 0
      rw [spinToConway_apply, hN j _ hj, Rat.cast_zero]
    rw [spinTopState_apply, hP_coe, LinearMap.lTensor_tmul,
      spinIso_frameJ_of_support (v := (fun j => spinToConway N j i : SpinIdx → ℂ)) hcol, ← hs,
      TensorProduct.tmul_smul]
  rw [mem_TPframe, mem_twFrameL, spinDict_apply, Submodule.coe_smul, map_smul, spinTopVec_apply,
    Submodule.coe_sum, map_sum]
  simp only [hterm]
  rw [← Finset.smul_sum]
  exact smul_comm _ _ _

/-- `κ_J = frameSign` is a sign `(−1)^{s₀}`. -/
theorem frameSign_eq_sgn : ∃ s₀ : ZMod 2, Extraspecial.sgn s₀ = frameSign := by
  have h := frameSign_mul_self
  have h' : (frameSign - 1) * (frameSign + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · exact ⟨0, by rw [Extraspecial.sgn_zero]; linear_combination -h1⟩
  · exact ⟨1, by rw [Extraspecial.sgn_one]; linear_combination -h1⟩

/-- ⭐ **The two halves of `W` are the two frame sectors**: there is `s₀ : ZMod 2` such that the
`W`-vectors supported on the rows `C₀ × {t}` go into `T_{s₀+t}⁺`, for `t = 0, 1`. -/
theorem spinDict_mem_TPframe_shift :
    ∃ s₀ : ZMod 2, ∀ (N : SpaceW) (t : ZMod 2), (∀ j i, j.1 ≠ t → N j i = 0) →
      spinDict N ∈ TPframe (s₀ + t) := by
  obtain ⟨s₀, hs₀⟩ := frameSign_eq_sgn
  refine ⟨s₀, fun N t hN => spinDict_mem_TPframe hN ?_⟩
  rw [Extraspecial.sgn_add, hs₀, sgnR_eq_sgn]

end VOA.Moonshine.GriessDictionary
