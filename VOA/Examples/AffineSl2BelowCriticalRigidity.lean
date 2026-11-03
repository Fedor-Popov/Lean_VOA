/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalGramMatrix

/-!
# Rigidity of the below-critical layer signs

This file **proves** the named input `LayerSignRigidity compactRealFamily` of
`AffineSl2BelowCriticalGradedUnitarity`.

1. *Reality.*  The canonical universal form satisfies `B(θu, θv) = B(u, v)` for the Chevalley
   involution `θ` and `conj B(ρu, ρv) = B(u, v)` for the compact real structure `ρ`
   (`universalForm_vacuumChevalley`, `universalForm_compactRho`).  Both follow from a uniqueness
   statement: a bilinear form on `V^k(sl₂)` is determined by its vacuum functional once every
   current mode `J^a_n` is skew-adjoint to `J^a_{-n}` (`bilinForm_eq_of_current_adj`).
2. *Hermitian Gram matrix.*  Hence the Gram matrix of `h(x,y) = B(ρx,y)` in the PBW monomials of a
   fixed energy is real symmetric (`gram_isHermitian`).
3. *Continuity.*  Its entries are polynomials in the level (`gram_eq_eval`), so the Gram matrix
   is continuous on the interval `(-∞, -2)`.
4. *Rigidity.*  `MatrixRigidity.matrixLayerSign_rigid` then transports the layer signs.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineSl2GeneralRigidity AffineSl2PBWWakimotoReduction
open AffineVOA.HighestModule
open Matrix MatrixRigidity BelowCriticalNoWall

noncomputable section

variable {k : ℂ} (hk : k + 2 ≠ 0)

/-! ## Uniqueness of current-adjoint bilinear forms -/

/-- A bilinear form on `V^k(sl₂)` with skew-adjoint currents is determined by its vacuum
functional. -/
theorem bilinForm_eq_of_current_adj (B₁ B₂ : LinearMap.BilinForm ℂ (WakModule k))
    (h₁ : ∀ (a : Fin 3) (n : ℤ) (u v : WakModule k), B₁ (J k a n u) v = -B₁ u (J k a (-n) v))
    (h₂ : ∀ (a : Fin 3) (n : ℤ) (u v : WakModule k), B₂ (J k a n u) v = -B₂ u (J k a (-n) v))
    (hvac : ∀ v, B₁ (vacuumA k) v = B₂ (vacuumA k) v) : B₁ = B₂ := by
  have hw : ∀ (w : List (Fin 3 × ℕ)) (v : WakModule k),
      B₁ (wordStateA k w) v = B₂ (wordStateA k w) v := by
    intro w
    induction w with
    | nil => exact hvac
    | cons b w ih =>
        intro v
        rw [wordStateA_cons, h₁, h₂, ih]
  apply LinearMap.ext_on_range (wordStateA_span k)
  intro w
  exact LinearMap.ext (hw w)

/-- The canonical universal form has skew-adjoint currents. -/
theorem universalForm_current_adj (a : Fin 3) (n : ℤ) (u v : WakModule k) :
    (universalForm k hk).form (J k a n u) v = -(universalForm k hk).form u (J k a (-n) v) := by
  have h := LQ43.weightOne_adj (universalForm_invariant k hk) (currentState_mem_grading k hk a)
    (LQ43.L1_grading_one k hk _ (currentState_mem_grading k hk a)) n u v
  rwa [smul_currentState_eq_J, smul_currentState_eq_J] at h

/-- The vacuum functional, computed weight by weight. -/
theorem vacuum_pair_of_grading_preserving (φ : WakModule k →+ WakModule k)
    (hφ : ∀ {n : ℤ} {v : WakModule k}, v ∈ (universal k hk).grading n →
      φ v ∈ (universal k hk).grading n)
    (f : ℂ → ℂ) (hf0 : ∀ c : ℂ, (universalForm k hk).form (vacuumA k) (φ (c • vacuumA k)) = f c)
    (hfadd : ∀ a b, f (a + b) = f a + f b) (hfz : f 0 = 0)
    (v : WakModule k) :
    (universalForm k hk).form (vacuumA k) (φ v) =
      f ((universalForm k hk).form (vacuumA k) v) := by
  have hx : v ∈ ⨆ n, (universal k hk).grading n := by
    rw [(universal k hk).isInternal.submodule_iSup_eq_top]; trivial
  refine Submodule.iSup_induction (universal k hk).grading
    (motive := fun y => (universalForm k hk).form (vacuumA k) (φ y) =
      f ((universalForm k hk).form (vacuumA k) y)) hx ?_ ?_ ?_
  · intro n y hy
    by_cases hn : n = 0
    · subst n
      have hvz : y ∈ ℂ ∙ (universal k hk).vacuum := by
        rw [← (universal k hk).vacuum_grade]; exact hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvz
      change (universalForm k hk).form (vacuumA k) (φ (c • vacuumA k)) =
        f ((universalForm k hk).form (vacuumA k) (c • vacuumA k))
      rw [hf0]
      congr 1
      rw [map_smul, smul_eq_mul]
      have hn1 := (universalForm_normalized k hk).vacuum_self
      change _ = c * (universalForm k hk).form (vacuumA k) (vacuumA k)
      rw [show (universalForm k hk).form (vacuumA k) (vacuumA k) = 1 from hn1, mul_one]
    · change (universalForm k hk).form (universal k hk).vacuum (φ y) =
        f ((universalForm k hk).form (universal k hk).vacuum y)
      rw [(universalForm k hk).orthogonal_of_ne (Ne.symm hn) (universal k hk).vacuum_mem (hφ hy),
        (universalForm k hk).orthogonal_of_ne (Ne.symm hn) (universal k hk).vacuum_mem hy, hfz]
  · simp [hfz]
  · intro a b ea eb
    rw [map_add, map_add, ea, eb, map_add, hfadd]

/-! ## Chevalley invariance -/

/-- The Chevalley involution preserves conformal weights. -/
theorem vacuumChevalley_mem_grading {n : ℤ} {v : WakModule k}
    (hv : v ∈ (universal k hk).grading n) : vacuumChevalley k v ∈ (universal k hk).grading n := by
  change vacuumChevalley k v ∈ gradingZA k n
  change v ∈ gradingZA k n at hv
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv ⊢
  rw [← vacuumChevalley_degree, hv, map_smul]

/-- `B(θu, θv) = B(u, v)`. -/
theorem universalForm_vacuumChevalley (u v : WakModule k) :
    (universalForm k hk).form (vacuumChevalley k u) (vacuumChevalley k v) =
      (universalForm k hk).form u v := by
  let B'' : LinearMap.BilinForm ℂ (WakModule k) :=
    (universalForm k hk).form.compl₁₂ (vacuumChevalley k) (vacuumChevalley k)
  have h := bilinForm_eq_of_current_adj B'' (universalForm k hk).form
    (fun a n u v => by
      simp only [B'', LinearMap.compl₁₂_apply, vacuumChevalley_current, map_neg,
        LinearMap.neg_apply, universalForm_current_adj hk, neg_neg])
    (universalForm_current_adj hk)
    (fun v => by
      simp only [B'', LinearMap.compl₁₂_apply, vacuumChevalley_vacuum]
      exact vacuum_pair_of_grading_preserving hk (vacuumChevalley k).toAddMonoidHom
        (vacuumChevalley_mem_grading hk) id
        (fun c => by
          change (universalForm k hk).form (vacuumA k) (vacuumChevalley k (c • vacuumA k)) = c
          rw [map_smul, vacuumChevalley_vacuum, map_smul, smul_eq_mul]
          rw [show (universalForm k hk).form (vacuumA k) (vacuumA k) = 1 from
            (universalForm_normalized k hk).vacuum_self, mul_one])
        (fun _ _ => rfl) rfl v)
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

/-! ## Compact-conjugation invariance -/

variable {hreal : (starRingEnd ℂ) k = k}

/-- The bilinear form `(u,v) ↦ conj B(ρu, ρv)`. -/
def conjForm (hreal : (starRingEnd ℂ) k = k) : LinearMap.BilinForm ℂ (WakModule k) :=
  LinearMap.mk₂ ℂ (fun u v => (starRingEnd ℂ) ((universalForm k hk).form (compactRho hreal u)
      (compactRho hreal v)))
    (fun u u' v => by simp [map_add])
    (fun c u v => by simp [compactRho_smul, map_smul, smul_eq_mul])
    (fun u v v' => by simp [map_add])
    (fun c u v => by simp [compactRho_smul, map_smul, smul_eq_mul])

/-- `conj B(ρu, ρv) = B(u, v)`. -/
theorem universalForm_compactRho (hreal : (starRingEnd ℂ) k = k) (u v : WakModule k) :
    (starRingEnd ℂ) ((universalForm k hk).form (compactRho hreal u) (compactRho hreal v)) =
      (universalForm k hk).form u v := by
  have h := bilinForm_eq_of_current_adj (conjForm hk hreal) (universalForm k hk).form
    (fun a n u v => by
      simp only [conjForm, LinearMap.mk₂_apply, compactRho_J, map_neg, LinearMap.neg_apply,
        universalForm_current_adj hk, neg_neg])
    (universalForm_current_adj hk)
    (fun v => by
      simp only [conjForm, LinearMap.mk₂_apply, compactRho_vacuum]
      have := vacuum_pair_of_grading_preserving hk (compactRho hreal)
        (fun hv => (compactRealStructure_isCompact hreal hk).rho_mem_grading hv)
        (starRingEnd ℂ)
        (fun c => by
          rw [compactRho_smul, compactRho_vacuum, map_smul, smul_eq_mul,
            show (universalForm k hk).form (vacuumA k) (vacuumA k) = 1 from
              (universalForm_normalized k hk).vacuum_self, mul_one])
        (fun a b => map_add _ a b) (map_zero _) v
      rw [this, Complex.conj_conj])
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

/-- The PBW conjugation fixes every creation word. -/
theorem basisConj_wordStateA (w : List (Fin 3 × ℕ)) :
    basisConj hreal (wordStateA k w) = wordStateA k w := by
  induction w with
  | nil => exact basisConj_vacuum hreal
  | cons b w ih => rw [wordStateA_cons, basisConj_J, ih]

theorem compactRho_currentPBWBasis (mu : CurrentIndex) :
    compactRho hreal (currentPBWBasis k hk mu) = vacuumChevalley k (currentPBWBasis k hk mu) := by
  rw [compactRho_apply, currentPBWBasis_apply, basisConj_wordStateA]

variable (hreal) in
/-- The Gram entries of the compact structure are twisted canonical pairings. -/
theorem gram_compact_apply {E : ℤ} (i j : EIdx E) :
    gram hk (compactRealStructure hreal hk) E i j =
      (universalForm k hk).form (vacuumChevalley k (currentPBWBasis k hk i.val))
        (currentPBWBasis k hk j.val) := by
  change (universalForm k hk).form (compactRho hreal (currentPBWBasis k hk i.val)) _ = _
  rw [compactRho_currentPBWBasis hk (hreal := hreal)]

variable (hreal) in
/-- **The compact Gram matrix is Hermitian** (indeed real symmetric). -/
theorem gram_isHermitian (E : ℤ) : (gram hk (compactRealStructure hreal hk) E).IsHermitian := by
  ext i j
  rw [conjTranspose_apply, gram_compact_apply, gram_compact_apply,
    vacuumChevalley_form_symm k hk]
  -- reality of the twisted pairing
  have hρθ : compactRho hreal (vacuumChevalley k (currentPBWBasis k hk i.val)) =
      currentPBWBasis k hk i.val := by
    rw [← compactRho_currentPBWBasis hk (hreal := hreal), compactRho_compactRho]
  have h := universalForm_compactRho hk hreal (vacuumChevalley k (currentPBWBasis k hk i.val))
    (currentPBWBasis k hk j.val)
  rw [hρθ, compactRho_currentPBWBasis hk (hreal := hreal)] at h
  have hθ := universalForm_vacuumChevalley hk (vacuumChevalley k (currentPBWBasis k hk i.val))
    (currentPBWBasis k hk j.val)
  rw [vacuumChevalley_involutive k hk] at hθ
  rw [hθ] at h
  exact h

/-! ## Polynomial dependence on the level -/

/-- The literal creation word of a PBW exponent. -/
def litWord (mu : CurrentIndex) : List (Fin 3 × ℤ) :=
  (orderedPBWColorWord mu).map (fun an => (an.1, -(an.2 : ℤ) - 1))

theorem litWord_state (mu : CurrentIndex) :
    NormalOrdering.currentWord (J k) (litWord mu) (universal k hk).vacuum =
      currentPBWBasis k hk mu := by
  rw [currentPBWBasis_apply]
  have hw (w : List (Fin 3 × ℕ)) :
      NormalOrdering.currentWord (J k) (w.map (fun an => (an.1, -(an.2 : ℤ) - 1)))
        (universal k hk).vacuum = wordStateA k w := by
    induction w with
    | nil => rfl
    | cons an w ih => simp only [List.map_cons, NormalOrdering.currentWord,
        Module.End.mul_apply, ih, wordStateA_cons]
  exact hw _

/-- The level-polynomial Gram entries. -/
def gramPoly (E : ℤ) (i j : EIdx E) : Polynomial ℂ :=
  ((-1 : ℂ) ^ (litWord i.val).length) •
    wordGramPolynomial (flipCurrentWord (litWord i.val)) (litWord j.val)

variable (hreal) in
/-- **The compact Gram matrix is polynomial in the level.** -/
theorem gram_eq_eval (hk0 : k ≠ 0) (E : ℤ) (i j : EIdx E) :
    gram hk (compactRealStructure hreal hk) E i j = (gramPoly E i j).eval k := by
  rw [gram_compact_apply, gramPoly, Polynomial.eval_smul, smul_eq_mul,
    wordGramPolynomial_universal k hk hk0, ← litWord_state hk i.val, ← litWord_state hk j.val]
  change (universalForm k hk).form
    (vacuumChevalley k (NormalOrdering.currentWord (J k) (litWord i.val) (vacuumA k))) _ = _
  rw [vacuumChevalley_word, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rfl

/-! ## Rigidity -/

/-- **The named rigidity input is a theorem.** -/
theorem layerSignRigidity_compact : LayerSignRigidity compactRealFamily := by
  intro E hLN x₀ hx₀ x₁ hx₁ h₀
  haveI : PreconnectedSpace (Set.Iio (-2 : ℝ)) := Subtype.preconnectedSpace isPreconnected_Iio
  let H : Set.Iio (-2 : ℝ) → Matrix (EIdx E) (EIdx E) ℂ := fun x =>
    gram (noncritical_of_lt x.2) (compactRealFamily x.1 x.2) E
  have hx0 : ∀ x : Set.Iio (-2 : ℝ), ((x.1 : ℝ) : ℂ) ≠ 0 := by
    intro x h
    have := congrArg Complex.re h
    simp at this
    have := x.2
    simp only [Set.mem_Iio] at this
    linarith
  have hHeq : H = fun x => fun i j => (gramPoly E i j).eval ((x.1 : ℝ) : ℂ) := by
    funext x i j
    exact gram_eq_eval (noncritical_of_lt x.2) (conj_ofReal x.1) (hx0 x) E i j
  have hcont : Continuous H := by
    rw [hHeq]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (Polynomial.continuous _).comp (Complex.continuous_ofReal.comp continuous_subtype_val)
  have hherm : ∀ x, (H x).IsHermitian := fun x =>
    gram_isHermitian (noncritical_of_lt x.2) (conj_ofReal x.1) E
  have hnd : ∀ x, MatrixStepNondeg (eLen E) (H x) := fun x =>
    matrixStepNondeg_of_layerNondeg (noncritical_of_lt x.2)
      (compactRealFamily_isCompact x.1 x.2) (hLN x.1 x.2)
  have h₀' := (layerPositive_iff_matrixLayerSign (noncritical_of_lt hx₀)
    (compactRealFamily_isCompact x₀ hx₀)).mp h₀
  refine (layerPositive_iff_matrixLayerSign (noncritical_of_lt hx₁)
    (compactRealFamily_isCompact x₁ hx₁)).mpr fun r => ?_
  exact matrixLayerSign_rigid H hcont hherm hnd r (t₀ := ⟨x₀, hx₀⟩) (t₁ := ⟨x₁, hx₁⟩) (h₀' r)

/-- **Below-critical graded unitarity, conditional only on the large-negative-level
anchor.**  For every real `k < -2`, `V^k(sl₂)` with its normalized canonical form, the
constructed compact real structure and the ordinary current-length flag is graded-unitary,
provided `LayerSignAnchor compactRealFamily` holds.

⚠ `#print axioms`-clean but conditional on `hanchor`.  Not unconditional. -/
theorem universal_gradedUnitary_belowCritical_of_anchor
    (hanchor : LayerSignAnchor compactRealFamily) (k : ℝ) (hk : k < -2) :
    GradedUnitary (universalForm (k : ℂ) (noncritical_of_lt hk)) (compactRealFamily k hk)
      (ordinaryFlag (k : ℂ) (noncritical_of_lt hk)) :=
  universal_gradedUnitary_belowCritical_compact hanchor layerSignRigidity_compact k hk

end

end AffineSl2BelowCritical

end VOA
