import VOA.Classification.COne.PlusSplitCharacterTable

/-! # Characters from explicit one-dimensional ordinary tops

Existence of the untwisted and twisted top models below remains OPEN.
The lattice ordinary modules are constructed in `LatticeModules`, but their
restriction/splitting and the required one-dimensional top calculations are
not supplied by that constructor. For the twisted models the source is
FLM Chapter 9 and Dong--Nagatomo arXiv:math/9807168, Section 2.2 and 5.1.
No classification or rationality premise is used in the proved implications.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusCharacterTable
open PlusUnitary

section General
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  (N : OrdVModule W M) {h : ℂ} (hlow : IsLowestWeight N h)
  (e : N.weight h ≃ₗ[ℂ] ℂ)

/-- A choice of coordinate on a one-dimensional lowest-weight space defines
its genuine Zhu character. -/
def topCharacter :
    letI := instRingA W; letI := instAlgebraA W; VOA.A W →ₐ[ℂ] ℂ := by
  letI := instRingA W
  letI := instAlgebraA W
  let f : VOA.A W →ₗ[ℂ] ℂ :=
    e.toLinearMap.comp ((LinearMap.applyₗ (e.symm 1)).comp (actA N hlow))
  have hy (y : N.weight h) : y = e y • e.symm 1 := by
    apply e.injective
    simp
  refine { f with map_zero' := f.map_zero, map_one' := ?_, map_mul' := ?_, commutes' := ?_ }
  · change e (actA N hlow (VOA.one W) (e.symm 1)) = 1
    rw [actA_one]; simp
  · intro a b
    change e (actA N hlow (a*b) (e.symm 1)) = _
    rw [actA_mul (zhuRingData_holds W) hlow]
    change e (actA N hlow a (actA N hlow b (e.symm 1))) = _
    conv_lhs => rw [hy (actA N hlow b (e.symm 1))]
    simp only [map_smul, smul_eq_mul]
    exact mul_comm _ _
  · intro c
    change f (algebraMap ℂ (VOA.A W) c) = c
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change c • e (actA N hlow (VOA.one W) (e.symm 1)) = c
    rw [actA_one]; simp

theorem topCharacter_mk_of_scalar (a : V) (c : ℂ)
    (ha : ∀ x : N.weight h, oMod N a (x : M) = c • (x : M)) :
    topCharacter N hlow e (VOA.mk W a) = c := by
  change e (actA N hlow (VOA.mk W a) (e.symm 1)) = c
  have he : actA N hlow (VOA.mk W a) (e.symm 1) = c • e.symm 1 := by
    apply Subtype.ext
    rw [actA_mk_apply_coe]
    exact ha _
  rw [he]; simp
end General

/-- Exact top data, including an actual irreducible ordinary module and a
one-dimensional lowest-weight space. No irreducible-completeness assertion. -/
def TopModel (m : ℕ) (hm : 1 ≤ m) (i : Label m) : Prop :=
  let v := values m (twistedScale m) i
  ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M)
    (N : OrdVModule (V2mPlus m hm) M),
    N.IsIrreducible ∧ IsLowestWeight N (v.1 : ℂ) ∧
    Nonempty (N.weight (v.1 : ℂ) ≃ₗ[ℂ] ℂ) ∧
    (∀ x : N.weight (v.1 : ℂ), oMod N (WP m hm) (x : M) = (v.2.1 : ℂ) • (x : M)) ∧
    (∀ x : N.weight (v.1 : ℂ), oMod N (EP m hm) (x : M) = (v.2.2 : ℂ) • (x : M))

def IsUntwisted {m : ℕ} : Label m → Prop
  | .inl _ => True
  | .inr i => i.val < 4

/-- The precise evaluation condition, on the actual quotient. -/
def HasValues (m : ℕ) (hm : 1 ≤ m) (i : Label m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    (VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ) → Prop :=
  fun χ => let v := values m (twistedScale m) i
    χ (VOA.mk (V2mPlus m hm) (gP m hm 0)) = (v.1 : ℂ) ∧
    χ (VOA.mk (V2mPlus m hm) (gP m hm 1)) = (v.2.1 : ℂ) ∧
    χ (VOA.mk (V2mPlus m hm) (gP m hm 2)) = (v.2.2 : ℂ)

theorem character_exists_of_topModel (m : ℕ) (hm : 1 ≤ m) (i : Label m)
    (hi : TopModel m hm i) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ, HasValues m hm i χ := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  obtain ⟨M, hM, hCM, N, _, hlow, ⟨e⟩, hW, hE⟩ := hi
  letI := hM
  letI := hCM
  refine ⟨topCharacter N hlow e, ?_, ?_, ?_⟩
  · apply topCharacter_mk_of_scalar
    intro x
    change oMod N (V2mPlus m hm).conformalVector (x : M) = _
    rw [oMod_conformalVector]
    exact N.L0_weight _ _ x.2
  · exact topCharacter_mk_of_scalar N hlow e _ _ hW
  · exact topCharacter_mk_of_scalar N hlow e _ _ hE

/-- Equal characters have equal table rows, hence equal labels. -/
theorem characters_injective (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m) :
    letI := instRingA (V2mPlus m hm); letI := instAlgebraA (V2mPlus m hm)
    ∀ χ : Label m → VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      (∀ i, HasValues m hm i (χ i)) → Function.Injective χ := by
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  intro χ hχ i j hij
  obtain ⟨hi0, hi1, hi2⟩ := hχ i
  obtain ⟨hj0, hj1, hj2⟩ := hχ j
  apply values_injective m hm2 _ (twistedScale_ne_zero m)
  have h0 := congrArg Complex.re (hi0.symm.trans ((congrArg
    (fun χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ =>
      χ (VOA.mk (V2mPlus m hm) (gP m hm 0))) hij).trans hj0))
  have h1 := congrArg Complex.re (hi1.symm.trans ((congrArg
    (fun χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ =>
      χ (VOA.mk (V2mPlus m hm) (gP m hm 1))) hij).trans hj1))
  have h2 := congrArg Complex.re (hi2.symm.trans ((congrArg
    (fun χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ =>
      χ (VOA.mk (V2mPlus m hm) (gP m hm 2))) hij).trans hj2))
  exact Prod.ext h0 (Prod.ext h1 h2)

end VOA.Classification.COne.PlusCharacterTable

namespace VOA.Classification.COne
open PlusCharacterTable

/-- OPEN: untwisted plus restrictions, half-lattice splitting, and top evaluations.
Dong--Nagatomo Proposition 2.3 and Section 5.1. -/
def V2mPlusUntwistedTopModels : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ i : Label m, IsUntwisted i → TopModel m hm i

/-- OPEN: the four rank-one twisted-sector modules and their explicit tops.
FLM Chapter 9; Dong--Nagatomo Section 2.2 and Section 5.1. -/
def V2mPlusTwistedTopModels : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m), 2 ≤ m → ∀ i : Label m, ¬ IsUntwisted i → TopModel m hm i

/-- Both explicit top-model inputs give the old, unchanged character target. -/
theorem zhuDistinctCharacters_of_topModels
    (hu : V2mPlusUntwistedTopModels) (ht : V2mPlusTwistedTopModels) :
    V2mPlusZhuDistinctCharacters := by
  classical
  intro m hm hm2
  letI := instRingA (V2mPlus m hm)
  letI := instAlgebraA (V2mPlus m hm)
  have hex : ∀ i : Label m, ∃ χ : VOA.A (V2mPlus m hm) →ₐ[ℂ] ℂ,
      HasValues m hm i χ := by
    intro i
    apply character_exists_of_topModel
    by_cases hi : IsUntwisted i
    · exact hu m hm hm2 i hi
    · exact ht m hm hm2 i hi
  choose χ hχ using hex
  let e : Label m ≃ Fin (m+7) := Fintype.equivFinOfCardEq (card_label m hm)
  exact ⟨χ ∘ e.symm, (characters_injective m hm hm2 χ hχ).comp e.symm.injective⟩

end VOA.Classification.COne
