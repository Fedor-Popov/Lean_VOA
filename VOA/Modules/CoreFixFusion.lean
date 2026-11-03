/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.Fusion
import VOA.Huang.FusionUnit

/-!
# The fusion coefficient `𝒩ᴾ_{MN}` from genuine intertwining operators  (Gannon 5.3.3)

A corrected fusion coefficient, as a leaf file alongside `Modules/Fusion.lean`.  The
`VOA.fusionCoeff` of `Modules/Fusion.lean` is
`finrank` of `IntertwinerSpace`, which imposes only the commutator formula (no truncation,
`L₋₁`-derivative or grading), and is identically `0`.  That is the library theorem
`fusionCoeff_eq_zero` below, moved here from the certificate
`Notes/Textbook/certificates/L12_FusionCoeffZero.lean`.

Here `fusionCoeffFHL A₁ A₂ A₃` is `finrank` of `intertwiningSpace A₁ A₂ A₃`
(`Huang/Intertwining.lean`): mode data satisfying the three Frenkel–Huang–Lepowsky axioms
(Def. 5.4.1) — truncation, the `L₋₁`-derivative property `(L₋₁w)₍ₙ₎ = -n w₍ₙ₋₁₎`, and the full
Jacobi identity.  It agrees with Huang's `fusionRule` by definition
(`fusionCoeffFHL_eq_fusionRule`).

⚠ As for every `Module.finrank`, the value is `0` on an infinite-dimensional space; read
`fusionCoeffFHL` together with a finite-dimensionality result (e.g.
`Huang.FusionUnit.finiteDimensional_intertwiningSpace_adjoint`,
`Huang.FusionC2.finiteDimensional_intertwiningSpace_of_C2`).

## Defect certificate
* `fusionCoeff_eq_zero` — the old `fusionCoeff` is identically `0`.

## Guard lemmas (the new definition is not identically zero)
* `fusionCoeffFHL_adjoint_self` — `𝒩ᴾ_{V P} = 1` for every irreducible lowest-weight module `P`.
* `one_le_fusionCoeffFHL_adjoint` — `𝒩ᴹ_{V M} ≥ 1` for every nonzero module `M` whose space of type
  `(M / V M)` is finite-dimensional (the module vertex operator `Y_M` is a nonzero intertwiner).
* `fusionCoeffFHL_adjoint_eq` — the unit axiom: `𝒩^{P₃}_{V P₂} = 1` iff `P₂ ≅ P₃`, else `0`.
-/

namespace VOA

universe u v₁ v₂ v₃

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
  [AddCommGroup M₃] [Module ℂ M₃]

/-- The **fusion coefficient** `𝒩^{M₃}_{M₁ M₂}` (Gannon 5.3.3): the dimension of the space of
intertwining operators of type `(M₃ / M₁ M₂)` in the sense of Frenkel–Huang–Lepowsky
(truncation, `L₋₁`-derivative, Jacobi identity; `intertwiningSpace`).  `Module.finrank`, so `0`
if that space is infinite-dimensional. -/
noncomputable def fusionCoeffFHL (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) : ℕ :=
  Module.finrank ℂ (intertwiningSpace A₁ A₂ A₃)

/-- Agreement with the Huang library: `fusionCoeffFHL` is Huang's `fusionRule`. -/
theorem fusionCoeffFHL_eq_fusionRule (A₁ : OrdVModule W M₁) (A₂ : OrdVModule W M₂)
    (A₃ : OrdVModule W M₃) : fusionCoeffFHL A₁ A₂ A₃ = fusionRule A₁ A₂ A₃ := rfl

/-- **Guard (non-vacuity)**: `𝒩ᴹ_{V M} ≥ 1` for a nonzero module `M`, given that the space of
intertwining operators of type `(M / V M)` is finite-dimensional: the module vertex operator
`Y_M` is a nonzero intertwiner (`moduleIntertwiner_ne_zero`). -/
theorem one_le_fusionCoeffFHL_adjoint (A : OrdVModule W M₁) [Nontrivial M₁]
    [FiniteDimensional ℂ (IntertwiningOperator (adjointModule W) A A)] :
    1 ≤ fusionCoeffFHL (adjointModule W) A A :=
  one_le_fusionRule_adjoint A

/-- **Guard (non-vacuity)**: `𝒩ᴾ_{V P} = 1` for every irreducible lowest-weight module `P`
(no finite-dimensionality hypothesis: it is proved in `Huang.FusionUnit`). -/
theorem fusionCoeffFHL_adjoint_self (P : LWModule W) (hP : P.IsIrreducibleLW) :
    fusionCoeffFHL (adjointModule W) P.isMod P.isMod = 1 :=
  Huang.FusionUnit.fusionRule_adjoint_self P hP

open Classical in
/-- **The unit axiom** for `fusionCoeffFHL`: for irreducible lowest-weight `P₂, P₃`,
`𝒩^{P₃}_{V P₂} = 1` if `P₂ ≅ P₃` and `0` otherwise. -/
theorem fusionCoeffFHL_adjoint_eq {P₂ P₃ : LWModule W} (h₂ : P₂.IsIrreducibleLW)
    (h₃ : P₃.IsIrreducibleLW) :
    fusionCoeffFHL (adjointModule W) P₂.isMod P₃.isMod
      = if Nonempty (ModuleEquiv W P₂.isMod P₃.isMod) then 1 else 0 :=
  Huang.FusionUnit.fusionRule_adjoint_eq h₂ h₃


/-! ## The uncorrected `fusionCoeff` is identically zero (certified)

Moved from `Notes/Textbook/certificates/L12_FusionCoeffZero.lean`.  If `Y ≠ 0` lies in
`IntertwinerSpace`, pick `Y s₀ u x ≠ 0`; restricting `Y` to the coset `s₀ + ℤ` and shifting the
exponent by `I·k` (`k : ℕ`) gives infinitely many linearly independent elements, because the
intertwining defect only relates `Y_s` to `Y_{s+p-j}`. -/

namespace CoreFixFusion

variable {M N P : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup P] [Module ℂ P]

/-- Restrict `Y` to the coset `s₀ + c + ℤ` after shifting the exponent by `c`. -/
noncomputable def shiftRestrict (Y : IntertwinerModes M N P) (s₀ c : ℂ) :
    IntertwinerModes M N P :=
  open Classical in fun s => if (∃ n : ℤ, s = s₀ + c + n) then Y (s - c) else 0

theorem coset_shift {s s₀ c : ℂ} (p : ℤ) (j : ℕ) :
    (∃ n : ℤ, s + p - j = s₀ + c + n) ↔ (∃ n : ℤ, s = s₀ + c + n) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n - p + j, by push_cast; linear_combination hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + p - j, by push_cast; linear_combination hn⟩

theorem shiftRestrict_mem (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P)
    {Y : IntertwinerModes M N P} (hY : Y ∈ IntertwinerSpace A B C) (s₀ c : ℂ) :
    shiftRestrict Y s₀ c ∈ IntertwinerSpace A B C := by
  classical
  have hY0 : intertwiningDefect A B C Y = 0 := hY
  change intertwiningDefect A B C (shiftRestrict Y s₀ c) = 0
  funext a p s u x
  have hYs := congrFun (congrFun (congrFun (congrFun (congrFun hY0 a) p) (s - c)) u) x
  simp only [intertwiningDefect, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hYs ⊢
  by_cases hs : ∃ n : ℤ, s = s₀ + c + n
  · have hsum : (∑ᶠ j : ℕ, intertwinerSummand A (shiftRestrict Y s₀ c) a p s u x j)
        = ∑ᶠ j : ℕ, intertwinerSummand A Y a p (s - c) u x j := by
      refine finsum_congr (fun j => ?_)
      simp only [intertwinerSummand, shiftRestrict]
      rw [if_pos ((coset_shift p j).mpr hs)]
      congr 3
      ring_nf
    rw [hsum]
    simp only [shiftRestrict, if_pos hs]
    exact hYs
  · have hsum : (∑ᶠ j : ℕ, intertwinerSummand A (shiftRestrict Y s₀ c) a p s u x j) = 0 := by
      rw [← finsum_zero (α := ℕ)]
      refine finsum_congr (fun j => ?_)
      simp only [intertwinerSummand, shiftRestrict]
      rw [if_neg (fun h => hs ((coset_shift p j).mp h))]
      simp
    rw [hsum]
    simp only [shiftRestrict, if_neg hs]
    simp

theorem shiftRestrict_eval (Y : IntertwinerModes M N P) (s₀ : ℂ) (k l : ℕ) :
    shiftRestrict Y s₀ (Complex.I * l) (s₀ + Complex.I * k)
      = if k = l then Y s₀ else 0 := by
  unfold shiftRestrict
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos ⟨0, by simp⟩, if_pos rfl]
    congr 1; ring_nf
  · rw [if_neg hkl, if_neg]
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp at him
    exact hkl (by exact_mod_cast him)

theorem not_finite_of_ne_zero (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P)
    {Y : IntertwinerModes M N P} (hY : Y ∈ IntertwinerSpace A B C) (hne : Y ≠ 0) :
    ¬ Module.Finite ℂ (IntertwinerSpace A B C) := by
  obtain ⟨s₀, u, x, hval⟩ : ∃ s₀ u x, Y s₀ u x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext fun s => LinearMap.ext fun u => LinearMap.ext fun x => h s u x)
  intro hfin
  let f : ℕ → IntertwinerSpace A B C := fun k =>
    ⟨shiftRestrict Y s₀ (Complex.I * k), shiftRestrict_mem A B C hY s₀ _⟩
  have hli : LinearIndependent ℂ f := by
    apply LinearIndependent.of_comp (IntertwinerSpace A B C).subtype
    rw [linearIndependent_iff']
    intro t g hsum i hi
    have h := congrArg (fun Z : IntertwinerModes M N P => Z (s₀ + Complex.I * i) u x) hsum
    simp only [Function.comp_apply, Submodule.subtype_apply, f] at h
    rw [Finset.sum_apply] at h
    simp only [Pi.smul_apply, shiftRestrict_eval, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.smul_apply] at h
    rw [Finset.sum_eq_single i] at h
    · have h' : g i • Y s₀ u x = 0 := by simpa using h
      exact (smul_eq_zero.mp h').resolve_right hval
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]
      simp
    · intro hin; exact absurd hi hin
  haveI := hli.finite
  exact not_finite ℕ

end CoreFixFusion

/-- **The S1 entry 4 defect, certified**: the old `fusionCoeff` (`Modules/Fusion.lean`) is
identically `0`. -/
theorem fusionCoeff_eq_zero {M N P : Type u} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] [AddCommGroup P] [Module ℂ P]
    (A : OrdVModule W M) (B : OrdVModule W N) (C : OrdVModule W P) :
    fusionCoeff A B C = 0 := by
  unfold fusionCoeff
  by_cases h : ∃ Y ∈ IntertwinerSpace A B C, Y ≠ 0
  · obtain ⟨Y, hY, hne⟩ := h
    exact Module.finrank_of_not_finite (CoreFixFusion.not_finite_of_ne_zero A B C hY hne)
  · push Not at h
    have hbot : IntertwinerSpace A B C = ⊥ := (Submodule.eq_bot_iff _).mpr h
    rw [hbot]
    exact finrank_bot ℂ _

/-- The old and new coefficients differ: on an irreducible lowest-weight module `P`,
`fusionCoeff (adjoint) P P = 0` but `fusionCoeffFHL (adjoint) P P = 1`. -/
theorem fusionCoeff_ne_fusionCoeffFHL (P : LWModule W) (hP : P.IsIrreducibleLW) :
    fusionCoeff (adjointModule W) P.isMod P.isMod
      ≠ fusionCoeffFHL (adjointModule W) P.isMod P.isMod := by
  rw [fusionCoeff_eq_zero, fusionCoeffFHL_adjoint_self P hP]
  exact zero_ne_one

end VOA
