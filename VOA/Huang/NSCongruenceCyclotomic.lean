/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Huang.NSCongruenceMain

/-!
# Cyclotomic membership of mixed indicators from orbit equivariance

`MixedRowCyclotomic` is Galois-equivalent to the primitive rescaling, so it has no cheaper direct
proof.  Here it
is derived from the `S` move along the orbit together with the modular-data statement
`MixedSCyclotomic` (the mixed S entries `D⁻¹ S_ik S_{j* l}` lie in `ℚ(ζ_N)`).  The mixed `T`
entries are `N`-th roots of unity and are handled unconditionally.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

namespace VOA.Huang.NSCongruence

open CategoryTheory MonoidalCategory Limits BraidedCategory
open VOA.Huang.NgSchauenburg
open scoped MatrixGroups

universe v u
attribute [-instance] hasRightDualUnit hasRightDualLeftDual

/-- The cyclotomic field `ℚ(ζ_N)` as a subalgebra of `ℂ`. -/
abbrev cycloField (N : ℕ) : Subalgebra ℚ ℂ :=
  Algebra.adjoin ℚ ({Complex.exp (2 * Real.pi * Complex.I / N)} : Set ℂ)

theorem mem_cycloField_of_pow_eq_one {N : ℕ} (hN : 0 < N) {x : ℂ} (hx : x ^ N = 1) :
    x ∈ cycloField N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N hN.ne'
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hx
  have hmem : Complex.exp (2 * Real.pi * Complex.I / N) ∈ cycloField N :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have := Subalgebra.pow_mem (cycloField N) hmem i
  rwa [hi] at this

section Entries
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- All matrix entries of a linear automorphism of `I → ℂ` lie in `K`. -/
def EntriesIn (K : Subalgebra ℚ ℂ) (L : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) : Prop :=
  ∀ p q : I, L (Pi.single q 1) p ∈ K

theorem entriesIn_apply_mem {K : Subalgebra ℚ ℂ} {L : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)}
    (hL : EntriesIn K L) {z : I → ℂ} (hz : ∀ q, z q ∈ K) (p : I) : L z p ∈ K := by
  have hz' : z = ∑ q, z q • (Pi.single q (1 : ℂ) : I → ℂ) := by
    ext r
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hz', map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Subalgebra.sum_mem _ fun q _ => Subalgebra.mul_mem _ (hz q) (hL p q)

theorem entriesIn_mul {K : Subalgebra ℚ ℂ} {L₁ L₂ : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)}
    (h₁ : EntriesIn K L₁) (h₂ : EntriesIn K L₂) : EntriesIn K (L₁ * L₂) := by
  intro p q
  rw [LinearEquiv.mul_apply]
  exact entriesIn_apply_mem h₁ (fun r => h₂ r q) p

theorem entriesIn_one (K : Subalgebra ℚ ℂ) : EntriesIn K (1 : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) := by
  intro p q
  change (Pi.single q (1 : ℂ) : I → ℂ) p ∈ K
  by_cases h : p = q
  · subst h; simp
  · simp [h]

theorem entriesIn_pow {K : Subalgebra ℚ ℂ} {L : (I → ℂ) ≃ₗ[ℂ] (I → ℂ)}
    (h : EntriesIn K L) (n : ℕ) : EntriesIn K (L ^ n) := by
  induction n with
  | zero => simpa using entriesIn_one K
  | succ n ih => rw [pow_succ]; exact entriesIn_mul ih h

end Entries

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]

open Classical in
/-- **Residual (cyclotomic mixed S).**  The entries `D⁻¹ S_ik S_{j* l}` of the mixed S matrix lie
in `ℚ(ζ_N)`, `N` the raw twist order.  A modular-data statement (Ng–Schauenburg 2010; DLN
Theorem II(i)); not proved here. -/
def MixedSCyclotomic (F : SphericalFusion C) (M : Modular F) : Prop :=
  ∀ p q : F.Label × F.Label, mixedS F M p q ∈ cycloField M.toRibbon.twistOrder

open Classical in
/-- Every element of the actual mixed representation has entries in `ℚ(ζ_N)`, given the mixed S
entries. -/
theorem mixedRepresentation_entriesIn (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (hc : MixedSCyclotomic F M) (γ : SL(2, ℤ)) :
    EntriesIn (cycloField M.toRibbon.twistOrder) (mixedRepresentation ρ γ) := by
  set N := M.toRibbon.twistOrder with hNdef
  have hN : 0 < N := M.toRibbon.finite_twist.1
  have hS : EntriesIn (cycloField N) (mixedRepresentation ρ ModularGroup.S) := by
    intro p q
    rw [mixedRepresentation_S F M ρ hr, Matrix.mulVec_single_one]
    exact hc p q
  have hT : EntriesIn (cycloField N) (mixedRepresentation ρ ModularGroup.T) := by
    intro p q
    rw [mixedRepresentation_T F M ρ hr]
    by_cases h : p = q
    · subst h
      simp only [Pi.single_eq_same, mul_one]
      apply mem_cycloField_of_pow_eq_one hN
      rw [div_pow, twistScalar_pow_twistOrder, twistScalar_pow_twistOrder, div_one]
    · simp [h]
  have hS4 : mixedRepresentation ρ ModularGroup.S ^ 4 = 1 := by
    rw [← map_pow]
    have : ModularGroup.S ^ 4 = (1 : SL(2, ℤ)) := by decide
    rw [this, map_one]
  have hTN := mixedRepresentation_T_period F M ρ hr
  have hg : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    simp [SpecialLinearGroup.SL2Z_generators]
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases (show x = ModularGroup.S ∨ x = ModularGroup.T by simpa using hx) with rfl | rfl
    · exact hS
    · exact hT
  | inv_mem x hx =>
    rcases (show x = ModularGroup.S ∨ x = ModularGroup.T by simpa using hx) with rfl | rfl
    · have he : mixedRepresentation ρ ModularGroup.S⁻¹ =
          mixedRepresentation ρ ModularGroup.S ^ 3 := by
        rw [map_inv, inv_eq_of_mul_eq_one_right]
        rw [← pow_succ', hS4]
      rw [he]; exact entriesIn_pow hS 3
    · have he : mixedRepresentation ρ ModularGroup.T⁻¹ =
          mixedRepresentation ρ ModularGroup.T ^ (N - 1) := by
        rw [map_inv, inv_eq_of_mul_eq_one_right]
        rw [← pow_succ', Nat.sub_add_cancel hN, hTN]
      rw [he]; exact entriesIn_pow hT _
  | one => rw [map_one]; exact entriesIn_one _
  | mul x y _ _ hx hy => rw [map_mul]; exact entriesIn_mul hx hy

open Classical in
/-- **`MixedRowCyclotomic` from the `S` move and cyclotomic mixed S entries**, given any modular
lift. -/
theorem mixedRowCyclotomic_of_SMove (F : SphericalFusion C) (M : Modular F)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) (hS : MixedSMoveOrbit F M)
    (hc : MixedSCyclotomic F M) : MixedRowCyclotomic F M := by
  intro a i j s _
  have he := orbitEquivariance_of_SMove F M hS ρ hr a
  let γ₀ : SL(2, ℤ) := ⟨!![s, -1; 1, 0], by simp [Matrix.det_fin_two]⟩
  have h := he γ₀ (Pi.single (i, j) 1)
  have hrow : rowAction 1 0 γ₀ = (s, -1) := by simp [rowAction, γ₀]
  rw [hrow] at h
  simp only [mixedRow] at h
  rw [equivariantIndicator_basis] at h
  rw [h]
  simp only [equivariantIndicator, LinearMap.coe_mk, AddHom.coe_mk]
  exact Subalgebra.sum_mem _ fun q _ => Subalgebra.mul_mem _
    (mixedRepresentation_entriesIn F M ρ hr hc _ q (i, j))
    (mixed_indicator_one_zero_mem F _ a q.1 q.2)

open Classical in
/-- **Projective congruence of every modular lift from the `S` move and cyclotomic mixed S
entries.** -/
theorem projectiveKernel_of_SMove_SCyclotomic (F : SphericalFusion C) (M : Modular F)
    (hS : MixedSMoveOrbit F M) (hc : MixedSCyclotomic F M)
    (ρ : SL(2, ℤ) →* ((F.Label → ℂ) ≃ₗ[ℂ] (F.Label → ℂ)))
    (hr : IsModularRepresentation F M ρ) :
    ProjectiveKernelContainsGamma ρ M.toRibbon.twistOrder :=
  projectiveKernel_of_SMove_cyclotomic F M hS (mixedRowCyclotomic_of_SMove F M ρ hr hS hc) ρ hr

end VOA.Huang.NSCongruence

namespace VOA.Huang.DLNBridge

open CategoryTheory MonoidalCategory Limits
open VOA.Huang.NgSchauenburg VOA.Huang.NSCongruence

universe u v w

/-- The `S` move and cyclotomic mixed S entries, for every modular category. -/
def NSMixedSResidualsAll : Prop :=
  ∀ (C : Type w) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
    [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    [HasKernels C] [HasFiniteBiproducts C] [BraidedCategory C]
    (F : SphericalFusion C) (M : Modular F),
    MixedSMoveOrbit F M ∧ MixedSCyclotomic F M

/-- **The kernel half of NS 6.8 from the `S` move and cyclotomic mixed S entries.** -/
theorem nsProjectiveKernelAll_of_SResiduals (h : NSMixedSResidualsAll.{v, w}) :
    NSProjectiveKernelAll.{v, w} := by
  intro C _ _ _ _ _ _ _ _ _ _ F M
  obtain ⟨hS, hc⟩ := h C F M
  exact ⟨M.toRibbon.twistOrder, M.toRibbon.finite_twist.1,
    fun ρ hρ => projectiveKernel_of_SMove_SCyclotomic F M hS hc ρ hρ⟩

/-- **Both classification inputs from the `S` move and cyclotomic mixed S entries.** -/
theorem dln_inputs_of_SResiduals (h : NSMixedSResidualsAll.{v, w})
    (hB : ZhuModularRepresentationInput.{u, v, w}) (hlift : MatrixDLNLifting)
    (hT : ZhuGaloisTwistInput.{u}) :
    VOA.Huang.CongruenceGaloisSplit.DLNCongruenceInput.{u} ∧
      VOA.Huang.CongruenceGaloisSplit.GaloisSymmetryNontrivialInput.{u} :=
  dln_inputs_of_NSKernel_twist (nsProjectiveKernelAll_of_SResiduals h) hB hlift hT

end VOA.Huang.DLNBridge
