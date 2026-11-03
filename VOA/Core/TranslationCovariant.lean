/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli
-/
import VOA.Core.Borcherds
import VOA.Core.BareVA

/-!
# Translation covariance, as a predicate on vertex algebras

`PreVertexAlgebra` (Gannon Def. 5.1.3(a)) has no translation-covariance axiom. Every
`VertexOperatorAlgebra` supplies it through VOA3, and the Borcherds identity
(`VertexOperatorAlgebra.jacobi`) is proved only at the VOA level. Adding the axiom to the bare
structure would touch about 31 construction files, so it is
a predicate instead.

* `PreVertexAlgebra.IsTranslationCovariant V`: `Y(T u, z) = ∂_z Y(u, z)` for all `u`, with the intrinsic
  translation operator `T u = u₍₋₂₎𝟙`.
* `VertexOperatorAlgebra.isTranslationCovariant`: every VOA is translation covariant.
* `TranslationCovariantCounterexample.not_isTranslationCovariant`: a 3-dimensional `PreVertexAlgebra`
  that is **not** translation covariant, and on which the Borcherds identity fails
  (`jacobi_fails`). So the predicate is a genuine restriction, and the bare structure does not
  satisfy Borcherds. The construction is vendored from
  `Notes/Textbook/certificates/L03_VertexAlgebraNoCovariance.lean`.
-/

namespace VOA

universe u

/-- **Translation covariance** of a vertex algebra: `Y(T u, z) = ∂_z Y(u, z)` for every `u`, where
`T u = u₍₋₂₎𝟙`. In modes: `(T u)₍ₙ₎ = -n · u₍ₙ₋₁₎`. -/
def PreVertexAlgebra.IsTranslationCovariant {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : PreVertexAlgebra 𝒱) : Prop :=
  ∀ v : 𝒱, V.Y (V.T v) = deriv (V.Y v)

/-- Mode form of translation covariance. -/
theorem PreVertexAlgebra.IsTranslationCovariant.smul_T {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {V : PreVertexAlgebra 𝒱} (h : V.IsTranslationCovariant) (v : 𝒱) (n : ℤ) (w : 𝒱) :
    V.smul (V.T v) n w = (-n) • V.smul v (n - 1) w := by
  rw [PreVertexAlgebra.smul_def, h v, mode_deriv, LinearMap.smul_apply]
  rfl

/-- **Every VOA is translation covariant**: `T = L₋₁` (`T_eq_Lneg1`) and VOA3. -/
theorem VertexOperatorAlgebra.isTranslationCovariant {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VertexOperatorAlgebra 𝒱) : W.toPreVertexAlgebra.IsTranslationCovariant := by
  intro v
  rw [VertexOperatorAlgebra.T_eq_Lneg1]
  exact W.translation v

end VOA

open VOA Module

namespace VOA.TranslationCovariantCounterexample

abbrev V := Fin 3 → ℂ

def mulA (u v : V) : V := ![u 0 * v 0, u 0 * v 1 + u 1 * v 0, u 0 * v 2 + u 2 * v 0]

@[simp] lemma mulA_0 (u v : V) : mulA u v 0 = u 0 * v 0 := rfl
@[simp] lemma mulA_1 (u v : V) : mulA u v 1 = u 0 * v 1 + u 1 * v 0 := rfl
@[simp] lemma mulA_2 (u v : V) : mulA u v 2 = u 0 * v 2 + u 2 * v 0 := rfl

def mulOp (u : V) : End ℂ V where
  toFun := mulA u
  map_add' a b := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c a := by funext i; fin_cases i <;> simp <;> ring

@[simp] lemma mulOp_apply (u v : V) : mulOp u v = mulA u v := rfl

def yb (u : V) : V := ![0, 0, u 1]

@[simp] lemma yb_0 (u : V) : yb u 0 = 0 := rfl
@[simp] lemma yb_1 (u : V) : yb u 1 = 0 := rfl
@[simp] lemma yb_2 (u : V) : yb u 2 = u 1 := rfl

def Yfun (u : V) : FormalDist (End ℂ V) :=
  fun k => if k = 0 then mulOp u else if k = 2 then mulOp (yb u) else 0

def Y : V →ₗ[ℂ] FormalDist (End ℂ V) where
  toFun := Yfun
  map_add' a b := by
    funext k
    show Yfun (a + b) k = Yfun a k + Yfun b k
    unfold Yfun
    split_ifs
    · ext v i; fin_cases i <;> simp <;> ring
    · ext v i; fin_cases i <;> simp [yb] <;> ring
    · simp
  map_smul' c a := by
    funext k
    show Yfun (c • a) k = c • Yfun a k
    unfold Yfun
    split_ifs
    · ext v i; fin_cases i <;> simp <;> ring
    · ext v i; fin_cases i <;> simp [yb] <;> ring
    · simp

lemma Y_apply (u : V) (k : ℤ) :
    Y u k = if k = 0 then mulOp u else if k = 2 then mulOp (yb u) else 0 := rfl

def vac : V := ![1, 0, 0]

def grading (n : ℤ) : Submodule ℂ V :=
  if n = 0 then
    { carrier := {v | v 2 = 0}, add_mem' := by intro a b ha hb; simp_all,
      zero_mem' := by simp, smul_mem' := by intro c a ha; simp_all }
  else if n = 2 then
    { carrier := {v | v 0 = 0 ∧ v 1 = 0}, add_mem' := by intro a b ha hb; simp_all,
      zero_mem' := by simp, smul_mem' := by intro c a ha; simp_all }
  else ⊥

lemma mem_g0 (v : V) : v ∈ grading 0 ↔ v 2 = 0 := by simp [grading]
lemma mem_g2 (v : V) : v ∈ grading 2 ↔ v 0 = 0 ∧ v 1 = 0 := by simp [grading]
lemma g_other {n : ℤ} (h0 : n ≠ 0) (h2 : n ≠ 2) : grading n = ⊥ := by
  simp [grading, h0, h2]

lemma eq_zero_of_mem_other {n : ℤ} (h0 : n ≠ 0) (h2 : n ≠ 2) {v : V} (hv : v ∈ grading n) :
    v = 0 := by
  rw [g_other h0 h2] at hv; exact (Submodule.mem_bot ℂ).mp hv

lemma isInternal : DirectSum.IsInternal grading := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro i
    rw [Submodule.disjoint_def]
    intro v hv hsup
    by_cases h0 : i = 0
    · subst h0
      have hle : (⨆ j, ⨆ (_ : j ≠ (0:ℤ)), grading j) ≤ grading 2 := by
        refine iSup_le fun j => iSup_le fun hj => ?_
        by_cases h2 : j = 2
        · subst h2; exact le_rfl
        · rw [g_other hj h2]; exact bot_le
      have h2' := (mem_g2 v).mp (hle hsup)
      have h1 := (mem_g0 v).mp hv
      funext k; fin_cases k <;> simp_all
    · by_cases h2 : i = 2
      · subst h2
        have hle : (⨆ j, ⨆ (_ : j ≠ (2:ℤ)), grading j) ≤ grading 0 := by
          refine iSup_le fun j => iSup_le fun hj => ?_
          by_cases h0 : j = 0
          · subst h0; exact le_rfl
          · rw [g_other h0 hj]; exact bot_le
        have h1 := (mem_g0 v).mp (hle hsup)
        have h2' := (mem_g2 v).mp hv
        funext k; fin_cases k <;> simp_all
      · exact eq_zero_of_mem_other h0 h2 hv
  · rw [eq_top_iff]
    intro v _
    have hv : v = ![v 0, v 1, 0] + ![0, 0, v 2] := by
      funext k; fin_cases k <;> simp
    rw [hv]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_iSup_of_mem (0:ℤ) ((mem_g0 _).mpr (by simp))
    · exact Submodule.mem_iSup_of_mem (2:ℤ) ((mem_g2 _).mpr (by simp))

lemma mode_Y (u : V) (n : ℤ) :
    mode (Y u) n = if n = -1 then mulOp u else if n = -3 then mulOp (yb u) else 0 := by
  rw [mode_apply, Y_apply]
  by_cases h1 : n = -1
  · subst h1; simp
  · by_cases h3 : n = -3
    · subst h3; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg h1, if_neg h3]

lemma mulOp_zero : mulOp 0 = 0 := by ext v i; fin_cases i <;> simp

lemma mulOp_comm (a b : V) : mulOp a * mulOp b = mulOp b * mulOp a := by
  ext v i; fin_cases i <;> simp [Module.End.mul_apply] <;> ring

lemma Y_eq_mulOp (u : V) (k : ℤ) : ∃ w, Y u k = mulOp w := by
  rw [Y_apply]
  split_ifs
  · exact ⟨u, rfl⟩
  · exact ⟨yb u, rfl⟩
  · exact ⟨0, mulOp_zero.symm⟩

/-- The counterexample vertex algebra: `V = span{𝟙, x, y}`, the commutative algebra with
`x² = xy = y² = 0`, and `Y(u,z)` multiplication by `φ_z(u)` with `φ_z(x) = x + z²y`. -/
def VA : PreVertexAlgebra V where
  grading := grading
  isInternal := isInternal
  finrank := fun _ => inferInstance
  Y := Y
  vacuum := vac
  vacuum_mem := (mem_g0 _).mpr (by simp [vac])
  grading_mode := by
    intro k ℓ u hu v hv n
    rw [mode_Y]
    -- reduce to the two nonzero grades for u and v
    by_cases hk : k = 0 ∨ k = 2
    · by_cases hl : ℓ = 0 ∨ ℓ = 2
      · split_ifs with h1 h3
        · subst h1
          rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
          · have := (mem_g0 u).mp hu; have := (mem_g0 v).mp hv
            rw [show (0:ℤ) + 0 - -1 - 1 = 0 by norm_num, mem_g0]; simp_all
          · have := (mem_g0 u).mp hu; have := (mem_g2 v).mp hv
            rw [show (0:ℤ) + 2 - -1 - 1 = 2 by norm_num, mem_g2]; simp_all
          · have := (mem_g2 u).mp hu; have := (mem_g0 v).mp hv
            rw [show (2:ℤ) + 0 - -1 - 1 = 2 by norm_num, mem_g2]; simp_all
          · have := (mem_g2 u).mp hu; have := (mem_g2 v).mp hv
            have hz : mulOp u v = 0 := by funext i; fin_cases i <;> simp_all
            rw [hz]; exact Submodule.zero_mem _
        · subst h3
          rcases hk with rfl | rfl <;> rcases hl with rfl | rfl
          · have := (mem_g0 u).mp hu; have := (mem_g0 v).mp hv
            rw [show (0:ℤ) + 0 - -3 - 1 = 2 by norm_num, mem_g2]; simp_all
          · have := (mem_g0 u).mp hu; have := (mem_g2 v).mp hv
            have hz : mulOp (yb u) v = 0 := by funext i; fin_cases i <;> simp_all
            rw [hz]; exact Submodule.zero_mem _
          · have := (mem_g2 u).mp hu; have := (mem_g0 v).mp hv
            have hz : mulOp (yb u) v = 0 := by funext i; fin_cases i <;> simp_all
            rw [hz]; exact Submodule.zero_mem _
          · have := (mem_g2 u).mp hu; have := (mem_g2 v).mp hv
            have hz : mulOp (yb u) v = 0 := by funext i; fin_cases i <;> simp_all
            rw [hz]; exact Submodule.zero_mem _
        · exact Submodule.zero_mem _
      · push Not at hl
        have := eq_zero_of_mem_other hl.1 hl.2 hv
        subst this; rw [map_zero]; exact Submodule.zero_mem _
    · push Not at hk
      have := eq_zero_of_mem_other hk.1 hk.2 hu
      subst this
      have h0 : mode (Y 0) n = 0 := by rw [map_zero]; rfl
      rw [← mode_Y, h0]; exact Submodule.zero_mem _
  vacuum_Y := by
    funext k
    rw [Y_apply, FormalDist.one_apply]
    by_cases h0 : k = 0
    · rw [if_pos h0, if_pos h0]; ext v i; fin_cases i <;> simp [vac]
    · rw [if_neg h0, if_neg h0]
      split_ifs
      · ext v i; fin_cases i <;> simp [vac, yb]
      · rfl
  creation := by
    intro u
    refine ⟨?_, fun n hn => ?_⟩
    · rw [mode_Y, if_pos rfl]; funext i; fin_cases i <;> simp [vac]
    · rw [mode_Y, if_neg (by omega), if_neg (by omega)]; rfl
  locality := by
    intro u v
    refine local_of_bracketDist_eq_zero ?_
    funext m n
    obtain ⟨a, ha⟩ := Y_eq_mulOp u m
    obtain ⟨b, hb⟩ := Y_eq_mulOp v n
    rw [bracketDist_apply, ha, hb, mulOp_comm, sub_self]
    rfl
  regularity := by
    intro u v
    refine ⟨0, fun n hn => ?_⟩
    rw [mode_Y, if_neg (by omega), if_neg (by omega)]; rfl

def xx : V := ![0, 1, 0]

/-- The Borcherds identity, in exactly the form of `VertexOperatorAlgebra.jacobi`, FAILS for
`VA` at `(u,v,x,ℓ,m,n) = (x, 1, 1, -2, 0, -2)`. -/
theorem jacobi_fails :
    ¬ ((∑ᶠ i : ℤ, (negOnePow i * cbz (-2) i) •
        (VA.smul xx ((-2) + 0 - i) (VA.smul vac ((-2) + i) vac)
          - negOnePow (-2) • VA.smul vac ((-2) + (-2) - i) (VA.smul xx (0 + i) vac)))
      = ∑ᶠ i : ℤ, cbz 0 i • VA.smul (VA.smul xx ((-2) + i) vac) (0 + (-2) - i) vac) := by
  have hvac : VA.vacuum = vac := rfl
  have hsv : ∀ k : ℤ, VA.smul vac k vac = if k = -1 then vac else 0 := by
    intro k; rw [← hvac, PreVertexAlgebra.smul_vacuum_left]
  have hxpos : ∀ i : ℤ, 0 ≤ i → VA.smul xx i vac = 0 := by
    intro i hi; rw [← hvac]; exact PreVertexAlgebra.smul_vacuum_nonneg VA xx hi
  have hx2 : VA.smul xx (-2) vac = 0 := by
    show mode (Y xx) (-2) vac = 0
    rw [mode_Y, if_neg (by norm_num), if_neg (by norm_num)]; rfl
  have hx3 : VA.smul xx (-3) vac = ![0, 0, 1] := by
    show mode (Y xx) (-3) vac = _
    rw [mode_Y, if_neg (by norm_num), if_pos rfl]
    funext i; fin_cases i <;> simp [xx, vac, yb]
  have hR : (∑ᶠ i : ℤ, cbz 0 i • VA.smul (VA.smul xx ((-2) + i) vac) (0 + (-2) - i) vac) = 0 := by
    rw [finsum_eq_single _ (0 : ℤ) (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
    rw [show (-2 : ℤ) + 0 = -2 by norm_num, hx2, PreVertexAlgebra.smul_zero_left, smul_zero]
  have hL : (∑ᶠ i : ℤ, (negOnePow i * cbz (-2) i) •
        (VA.smul xx ((-2) + 0 - i) (VA.smul vac ((-2) + i) vac)
          - negOnePow (-2) • VA.smul vac ((-2) + (-2) - i) (VA.smul xx (0 + i) vac)))
        = (2 : ℂ) • ![0, 0, 1] := by
    rw [finsum_eq_single _ (1 : ℤ) (fun i hi => ?_)]
    · rw [hsv, if_pos (by norm_num), show (-2 : ℤ) + 0 - 1 = -3 by norm_num, hx3,
        hxpos _ (by norm_num), PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero]
      congr 1
      rw [cbz_apply_nonneg _ (by norm_num)]
      simp [negOnePow, gBinom]
    · rcases lt_or_ge i 0 with hneg | hnn
      · rw [cbz_apply_neg _ hneg, mul_zero, zero_smul]
      · rw [hsv, if_neg (by omega), PreVertexAlgebra.smul_zero_right, hxpos _ (by omega),
          PreVertexAlgebra.smul_zero_right, smul_zero, sub_zero, smul_zero]
  rw [hL, hR]
  intro h
  have := congrFun h 2
  simp at this

/-- Translation covariance fails: `T x = 0` but `∂_z Y(x,z) ≠ 0`. -/
theorem translation_fails : VA.Y (VA.T xx) ≠ deriv (VA.Y xx) := by
  intro h
  have h1 := congrArg (fun F : FormalDist (End ℂ V) => F 1 vac 2) h
  simp only at h1
  have hT : VA.T xx = 0 := by
    funext i
    show VA.smul xx (-2) vac i = 0
    show mode (Y xx) (-2) vac i = 0
    rw [mode_Y, if_neg (by norm_num), if_neg (by norm_num)]; rfl
  rw [hT, map_zero, deriv_apply] at h1
  change (0 : V) 2 = ((1 + 1 : ℤ) • Y xx (1 + 1)) vac 2 at h1
  rw [Y_apply, if_neg (by norm_num), if_pos (by norm_num)] at h1
  simp [xx, vac, yb] at h1


/-- The counterexample is **not** translation covariant. -/
theorem not_isTranslationCovariant : ¬ VA.IsTranslationCovariant :=
  fun h => translation_fails (h xx)

end VOA.TranslationCovariantCounterexample

section AxiomAudit
#print axioms VOA.VertexOperatorAlgebra.isTranslationCovariant
#print axioms VOA.TranslationCovariantCounterexample.VA
#print axioms VOA.TranslationCovariantCounterexample.not_isTranslationCovariant
#print axioms VOA.TranslationCovariantCounterexample.jacobi_fails
end AxiomAudit
