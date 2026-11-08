/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessSign
import Mathlib.RingTheory.TensorProduct.Free

/-!
# The untwisted Griess dictionary is a `ℂ`-linear isomorphism onto `(V_Λ⁺)₂`

Let `U = {u ∈ SpaceB | u.2.2 = 0}` (`untwistedSub`), the `W = 0` part `symMat × SpaceX` of Axiom's
rational Griess algebra, and `Φ = untwistedDict griessShortSign : U → V_Λ⁺` the untwisted
dictionary with the sign map of `MoonshineCNGriessSign`.  This file proves that the `ℂ`-linear
extension of `Φ` is an isomorphism `ℂ ⊗[ℚ] U ≅ (V_Λ⁺)₂`:

* **injectivity** — `bform` is positive definite (`bform_self_eq_zero`), so it has dual bases on
  `U`; pairing a vanishing `ℂ`-combination of the `Φ(bₖ)` with `Φ` of a dual basis vector and using
  `natForm`-isometry (`untwistedDict_form`) kills every coefficient
  (`linearIndependent_untwistedImage`);
* **surjectivity** — `(V_Λ⁺)₂` is spanned by the frame states `qP a b` and the `x_α`, `|α|² = 4`
  (`leechVOAPlus_grading_two_eq_span`).  Every `x_α` is `ζ_c⁻¹ Φ(e_c)` for the short class `c` of
  `±α` (bijectivity of `phi0`, `exists_shortIdx_of_normFour`); every frame state is a Conway
  state `Q_C(A)` (the Conway frame is invertible, `conwayFrame_mul_transpose`: `FFᵀ = 8`), and
  `Q_C(Eᵢⱼ) = ½ Φ(E_{πi,πj} + E_{πj,πi})` (`span_untwistedImage`).

## Main results
* `untwistedBasisC : Basis _ ℂ (leechVOAPlus.grading 2)` — the images of a `ℚ`-basis of `U`.
* ⭐ `untwistedIsoC : ℂ ⊗[ℚ] untwistedSub ≃ₗ[ℂ] leechVOAPlus.grading 2`, with
  ⭐ `untwistedIsoC_tmul : untwistedIsoC (1 ⊗ₜ u) = Φ u`.
* `finrank_leechPlus_two` — `dim_ℂ (V_Λ⁺)₂ = dim_ℚ U`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop VOA.Moonshine.TrialityTw
open VOA.LatGen VOA.IntegralLattice HeisenbergN
open VOA.Moonshine.ConwayNorton.M8
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin
open VOA.Moonshine.MonsterGriess.LeechMatch (vec leechEquiv piPerm leechEquiv_mem_minVecs_iff
  classOf_eq_iff)
open Matrix
open scoped TensorProduct

/-! ## §1  The rational side: the `W = 0` subspace and positivity of `bform` -/

/-- The `W = 0` part `symMat × SpaceX × {0}` of `SpaceB`. -/
def untwistedSub : Submodule ℚ SpaceB :=
  LinearMap.ker ((LinearMap.snd ℚ SpaceX SpaceW).comp (LinearMap.snd ℚ symMat (SpaceX × SpaceW)))

theorem mem_untwistedSub {u : SpaceB} : u ∈ untwistedSub ↔ u.2.2 = 0 := by
  rw [untwistedSub, LinearMap.mem_ker]
  rfl

/-- **`bform` is positive definite**: `bform u u = 0` forces `u = 0`. -/
theorem bform_self_eq_zero {u : SpaceB} (h : bform u u = 0) : u = 0 := by
  obtain ⟨A, x, N⟩ := u
  have hA : trace ((A : Matrix (Fin 24) (Fin 24) ℚ) * (A : Matrix (Fin 24) (Fin 24) ℚ))
      = ∑ i, ∑ j, (A : Matrix (Fin 24) (Fin 24) ℚ) i j * (A : Matrix (Fin 24) (Fin 24) ℚ) i j := by
    simp only [trace, diag, mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hs : (A : Matrix (Fin 24) (Fin 24) ℚ) j i = (A : Matrix (Fin 24) (Fin 24) ℚ) i j := by
      have := congrFun (congrFun (mem_symMat.1 A.2) i) j
      rwa [transpose_apply] at this
    rw [hs]
  rw [bform_apply] at h
  simp only at h
  rw [hA] at h
  have h1 : 0 ≤ ∑ i, ∑ j, (A : Matrix (Fin 24) (Fin 24) ℚ) i j * (A : Matrix (Fin 24) (Fin 24) ℚ) i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have h2 : 0 ≤ ∑ c, x c * x c := Finset.sum_nonneg fun c _ => mul_self_nonneg _
  have h3 : 0 ≤ ∑ j, ∑ i, N j i * N j i :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have e1 : ∑ i, ∑ j, (A : Matrix (Fin 24) (Fin 24) ℚ) i j * (A : Matrix (Fin 24) (Fin 24) ℚ) i j = 0 := by
    linarith
  have e2 : ∑ c, x c * x c = 0 := by linarith
  have e3 : ∑ j, ∑ i, N j i * N j i = 0 := by linarith
  have hA0 : A = 0 := by
    apply Subtype.ext
    ext i j
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_self_nonneg ((A : Matrix (Fin 24) (Fin 24) ℚ) i j))).1 e1 i (Finset.mem_univ _)
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_self_nonneg ((A : Matrix (Fin 24) (Fin 24) ℚ) i j))).1 h4 j (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 h5
  have hx0 : x = 0 := by
    funext c
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_self_nonneg (x c))).1 e2 c
      (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 h4
  have hN0 : N = 0 := by
    ext j i
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun i _ =>
      mul_self_nonneg (N j i))).1 e3 j (Finset.mem_univ _)
    have h5 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (N j i))).1 h4 i
      (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 h5
  rw [hA0, hx0, hN0]
  rfl

theorem bform_restrict_apply (u w : untwistedSub) :
    bform.restrict untwistedSub u w = bform (u : SpaceB) (w : SpaceB) := rfl

theorem bform_restrict_nondegenerate : (bform.restrict untwistedSub).Nondegenerate := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h := hu u
    rw [bform_restrict_apply] at h
    exact Subtype.ext (bform_self_eq_zero h)
  · have h := hu u
    rw [bform_restrict_apply] at h
    exact Subtype.ext (bform_self_eq_zero h)

/-! ## §2  `ℚ`-homogeneity and the images of a `ℚ`-basis -/

theorem shortDict_smul (ζ : ShortIdx → ℂ) (q : ℚ) (x : SpaceX) :
    shortDict ζ (q • x) = (q : ℂ) • shortDict ζ x := by
  rw [shortDict_apply, shortDict_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  push_cast
  ring

theorem untwistedDict_smul (ζ : ShortIdx → ℂ) (q : ℚ) (u : SpaceB) :
    untwistedDict ζ (q • u) = (q : ℂ) • untwistedDict ζ u := by
  rw [untwistedDict_apply, untwistedDict_apply, smul_add]
  change matDict ((q • u.1 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) + shortDict ζ (q • u.2.1) = _
  rw [Submodule.coe_smul, matDict_smul, shortDict_smul]

/-- A `ℚ`-basis of the untwisted subspace. -/
noncomputable def untwistedBasisQ :
    Module.Basis (Fin (Module.finrank ℚ untwistedSub)) ℚ untwistedSub :=
  Module.finBasis ℚ untwistedSub

/-- The images `Φ(bₖ) ∈ V_Λ⁺` of the `ℚ`-basis vectors. -/
noncomputable def untwistedImage (k : Fin (Module.finrank ℚ untwistedSub)) : VPlus :=
  untwistedDict griessShortSign (untwistedBasisQ k : SpaceB)

theorem untwistedDict_eq_sum (u : untwistedSub) :
    untwistedDict griessShortSign (u : SpaceB)
      = ∑ k, ((untwistedBasisQ.repr u k : ℚ) : ℂ) • untwistedImage k := by
  conv_lhs => rw [← untwistedBasisQ.sum_repr u]
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, untwistedDict_smul]
  rfl

/-- ⭐ **The images of a `ℚ`-basis are `ℂ`-linearly independent** (from the isometry property and
positive definiteness of `bform`). -/
theorem linearIndependent_untwistedImage : LinearIndependent ℂ untwistedImage := by
  classical
  rw [linearIndependent_iff']
  intro s g hg l hl
  set wl := (bform.restrict untwistedSub).dualBasis bform_restrict_nondegenerate untwistedBasisQ l
  have hk : ∀ k, plusForm (untwistedDict griessShortSign (wl : SpaceB)) (untwistedImage k)
      = 2 * ((if k = l then 1 else 0 : ℚ) : ℂ) := by
    intro k
    rw [untwistedImage, untwistedDict_form shortSignDictionary_griessShortSign
      (mem_untwistedSub.1 wl.2) (mem_untwistedSub.1 (untwistedBasisQ k).2)]
    have := LinearMap.BilinForm.apply_dualBasis_left bform_restrict_nondegenerate untwistedBasisQ l k
    rw [bform_restrict_apply] at this
    rw [this]
  have h := congrArg (fun y => plusForm (untwistedDict griessShortSign (wl : SpaceB)) y) hg
  simp only [map_sum, map_smul, map_zero, smul_eq_mul, hk] at h
  rw [Finset.sum_eq_single l (fun k _ hkl => by rw [if_neg hkl]; simp)
    (fun h' => absurd hl h')] at h
  rw [if_pos rfl] at h
  simpa using h

theorem untwistedDict_mem_span {u : SpaceB} (hu : u.2.2 = 0) :
    untwistedDict griessShortSign u ∈ Submodule.span ℂ (Set.range untwistedImage) := by
  have h := untwistedDict_eq_sum ⟨u, mem_untwistedSub.2 hu⟩
  change untwistedDict griessShortSign u = _ at h
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-! ## §3  Spanning `(V_Λ⁺)₂` -/

/-- `Q_C(Eᵢⱼ) = ½ Φ(E_{πi,πj} + E_{πj,πi})`. -/
theorem conwayQuad_single (i j : Fin 24) :
    conwayQuad (Matrix.single i j (1 : ℂ)) = (1 / 2 : ℂ) • matDict
      (Matrix.single (piPerm i) (piPerm j) (1 : ℚ) + Matrix.single (piPerm j) (piPerm i) 1) := by
  have h : axiomToConway (Matrix.single (piPerm i) (piPerm j) (1 : ℚ)
      + Matrix.single (piPerm j) (piPerm i) 1)
      = Matrix.single i j (1 : ℂ) + Matrix.single j i 1 := by
    ext k l
    simp only [axiomToConway_apply, Matrix.add_apply, Matrix.single_apply,
      EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp
  rw [matDict_apply, h, map_add, ← transpose_single i j (1 : ℂ), conwayQuad_transpose,
    ← two_smul ℂ, smul_smul]
  norm_num

theorem conwayQuad_single_mem_span (i j : Fin 24) :
    conwayQuad (Matrix.single i j (1 : ℂ)) ∈ Submodule.span ℂ (Set.range untwistedImage) := by
  rw [conwayQuad_single]
  refine Submodule.smul_mem _ _ ?_
  have hS : (Matrix.single (piPerm i) (piPerm j) (1 : ℚ) + Matrix.single (piPerm j) (piPerm i) 1)
      ∈ symMat := by
    rw [mem_symMat, transpose_add, transpose_single, transpose_single, add_comm]
  have h := untwistedDict_mem_span (u := symBlock ⟨_, hS⟩) rfl
  rwa [untwistedDict_symBlock] at h

theorem conwayQuad_mem_span (A : Matrix (Fin 24) (Fin 24) ℂ) :
    conwayQuad A ∈ Submodule.span ℂ (Set.range untwistedImage) := by
  rw [matrix_eq_sum_single A, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (conwayQuad_single_mem_span i j)

/-- The Conway frame is invertible: `FFᵀ = 8` (from `FᵀF = 8` and `rank Λ = 24`). -/
theorem conwayFrame_mul_transpose :
    conwayFrame * conwayFrameᵀ = (8 : ℂ) • (1 : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) := by
  have e : Fin 24 ≃ Fin (rank leech) := finCongr leech_rank.symm
  have h1 : ((8 : ℂ)⁻¹ • conwayFrameᵀ) * conwayFrame = 1 := by
    rw [Matrix.smul_mul, conwayFrame_transpose_mul, smul_smul]
    norm_num
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  rw [Matrix.mul_smul] at h2
  calc conwayFrame * conwayFrameᵀ
      = (8 : ℂ) • ((8 : ℂ)⁻¹ • (conwayFrame * conwayFrameᵀ)) := by
        rw [smul_smul]
        norm_num
    _ = (8 : ℂ) • (1 : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) := by rw [h2]

/-- Every frame state is a Conway state: `Q(M) = Q_C(⅛ FᵀMF)`. -/
theorem frameQuad_eq_conwayQuad (M : Matrix (Fin (rank leech)) (Fin (rank leech)) ℂ) :
    frameQuad M = conwayQuad ((8 : ℂ)⁻¹ • (conwayFrameᵀ * M * conwayFrame)) := by
  rw [conwayQuad_apply, conwayToFrame_apply]
  congr 1
  have key : conwayFrame * (conwayFrameᵀ * M * conwayFrame) * conwayFrameᵀ = (64 : ℂ) • M := by
    calc conwayFrame * (conwayFrameᵀ * M * conwayFrame) * conwayFrameᵀ
        = (conwayFrame * conwayFrameᵀ) * M * (conwayFrame * conwayFrameᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (64 : ℂ) • M := by
          rw [conwayFrame_mul_transpose]
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
          norm_num
  rw [Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, smul_smul]
  norm_num

theorem qP_mem_span (a b : Fin (rank leech)) :
    qP a b ∈ Submodule.span ℂ (Set.range untwistedImage) := by
  rw [qP_eq_frameQuad, frameQuad_eq_conwayQuad]
  exact conwayQuad_mem_span _

/-- Every minimal vector is `±α_c` for a short coordinate `c` (bijectivity of `phi0`). -/
theorem exists_shortIdx_of_normFour {α : leech.carrier} (hα : leech.form α α = 4) :
    ∃ c : ShortIdx, shortVec c = α ∨ shortVec c = -α := by
  have hmin : (leechEquiv α : Fin 24 → ℤ) ∈ Code.minVecs := (leechEquiv_mem_minVecs_iff α).2 hα
  obtain ⟨p, hp⟩ := SpinLattice.phi0_bijective.2 (Code.classOf (leechEquiv α : Fin 24 → ℤ))
  let c : ShortIdx := ⟨p, ⟨_, hmin, hp.symm⟩⟩
  refine ⟨c, ?_⟩
  have hcl : Code.classOf (uvec c) = Code.classOf (leechEquiv α : Fin 24 → ℤ) := by
    rw [classOf_uvec, ← hp]
  rcases (classOf_eq_iff (uvec_mem_minVecs c) hmin).1 hcl with h | h
  · left
    apply leechEquiv.injective
    apply Subtype.ext
    rw [leechEquiv_shortVec, h]
  · right
    apply leechEquiv.injective
    apply Subtype.ext
    rw [leechEquiv_shortVec, h, map_neg]
    rfl

theorem griessShortSign_ne_zero (c : ShortIdx) : griessShortSign c ≠ 0 := by
  intro h
  have := griessShortSign_sq c
  rw [h] at this
  simp at this

theorem frameX0P_mem_span {α : leech.carrier} (hα : leech.form α α = 4) :
    frameX0P α ∈ Submodule.span ℂ (Set.range untwistedImage) := by
  classical
  obtain ⟨c, hc⟩ := exists_shortIdx_of_normFour hα
  have h1 : frameX0P α = (griessShortSign c)⁻¹ •
      untwistedDict griessShortSign (shortBlock (Pi.single c 1)) := by
    rw [untwistedDict_shortBlock, shortDict_apply, Finset.sum_eq_single c]
    · rw [Pi.single_eq_same, Rat.cast_one, one_mul, smul_smul,
        inv_mul_cancel₀ (griessShortSign_ne_zero c), one_smul]
      rcases hc with h | h
      · rw [h]
      · rw [h, frameX0P_neg_eq]
    · intro d _ hd
      rw [Pi.single_eq_of_ne hd, Rat.cast_zero, zero_mul, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ c) h
  rw [h1]
  exact Submodule.smul_mem _ _ (untwistedDict_mem_span rfl)

/-- ⭐ **The images span `(V_Λ⁺)₂`.** -/
theorem span_untwistedImage :
    Submodule.span ℂ (Set.range untwistedImage) = leechVOAPlus.grading 2 := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact untwistedDict_mem_grading_two _
  · rw [leechVOAPlus_grading_two_eq_span, Submodule.span_le]
    rintro _ (⟨p, rfl⟩ | ⟨α, hα, rfl⟩)
    · exact qP_mem_span p.1 p.2
    · exact frameX0P_mem_span hα

/-! ## §4  The `ℂ`-linear isomorphism -/

/-- **A `ℂ`-basis of `(V_Λ⁺)₂`**: the images of a `ℚ`-basis of the untwisted subspace. -/
noncomputable def untwistedBasisC :
    Module.Basis (Fin (Module.finrank ℚ untwistedSub)) ℂ (leechVOAPlus.grading 2) :=
  (Module.Basis.span linearIndependent_untwistedImage).map
    (LinearEquiv.ofEq _ _ span_untwistedImage)

theorem untwistedBasisC_apply (k : Fin (Module.finrank ℚ untwistedSub)) :
    (untwistedBasisC k : VPlus) = untwistedImage k := by
  simp [untwistedBasisC]

/-- ⭐ **The `ℂ`-linear extension of the untwisted dictionary**:
`ℂ ⊗[ℚ] U ≃ₗ[ℂ] (V_Λ⁺)₂`, `1 ⊗ bₖ ↦ Φ(bₖ)`. -/
noncomputable def untwistedIsoC : ℂ ⊗[ℚ] untwistedSub ≃ₗ[ℂ] leechVOAPlus.grading 2 :=
  (Algebra.TensorProduct.basis ℂ untwistedBasisQ).equiv untwistedBasisC (Equiv.refl _)

/-- ⭐ **`untwistedIsoC` extends the rational dictionary**: `untwistedIsoC (1 ⊗ u) = Φ u`. -/
theorem untwistedIsoC_tmul (u : untwistedSub) :
    (untwistedIsoC (1 ⊗ₜ u) : VPlus) = untwistedDict griessShortSign (u : SpaceB) := by
  rw [untwistedDict_eq_sum]
  conv_lhs => rw [← untwistedBasisQ.sum_repr u]
  rw [TensorProduct.tmul_sum, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TensorProduct.tmul_smul, ← algebraMap_smul ℂ (untwistedBasisQ.repr u k), map_smul,
    ← Algebra.TensorProduct.basis_apply, untwistedIsoC, Module.Basis.equiv_apply, Equiv.refl_apply,
    Submodule.coe_smul, untwistedBasisC_apply, eq_ratCast]

/-- `dim_ℂ (V_Λ⁺)₂ = dim_ℚ U`. -/
theorem finrank_leechPlus_two :
    Module.finrank ℂ (leechVOAPlus.grading 2) = Module.finrank ℚ untwistedSub := by
  rw [Module.finrank_eq_card_basis untwistedBasisC, Fintype.card_fin]

end VOA.Moonshine.GriessDictionary
