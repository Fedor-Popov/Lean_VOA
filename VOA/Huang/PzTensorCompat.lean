/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorCommutator

/-!
# The `P(1)`-compatibility condition — splitting `TauAssociator`

Huang–Lepowsky–Zhang (*Logarithmic tensor category theory IV*, Thm. 5.44) prove the Jacobi
identity for the `P(z)`-action `Y'_{P(z)}` on every functional `λ ∈ (W₁ ⊗ W₂)*` satisfying the
**`P(z)`-compatibility condition**: (a) lower truncation and (b) formula (5.141).  In the
homogeneous-pair presentation (`z = 1`, fixed intermediate weight) condition (b) is the transposed
associator formula of an intertwining map (`CompatFn`):

`G(a_ℓ w₁, w₂) + Σ_j C(ℓ,j)(−1)^{ℓ−j} G(w₁, a_j w₂) = Σ_k C(ℓ,k)(−1)^k Δᵀ(a_{ℓ−k}) G (w₁, w₂)`

for every homogeneous `a ∈ V` and **every** `ℓ ∈ ℤ` (for `ℓ ≥ 0` it is an algebraic identity; for
`ℓ < 0` it is the genuine content: the residue theorem for `(ζ − z₁)^ℓ` around the two inside
points, with the outside residues re-expanded through
`(ζ − z₁)^ℓ = Σ_k C(ℓ,k)(−u)^k (ζ − z₂)^{ℓ−k}`).
For `G = ⟨w', I(·⊗·)⟩` with `I` an honest intertwining map it is exactly the `m = 0` slice of the
intertwining-operator Jacobi identity.

This file splits the remaining input `PzTensorSpan.TauAssociator` into two named, TRUE
propositions of very different nature:

* `CoeffCompat W` (analytic input, coefficient level): every coefficient function `B_{n,k}(f,w₃)`
  of a product satisfies `CompatFn`.  Source: the left associator identity
  `AssocAssociator.prodValueZ_assoc_left` (proved, values) + the right associator
  (`AssocTauStable.coefFun_coproduct_holds`, proved) + the weight bound
  (`LogRemovalWeightBound.coefFun_eq_zero_of_re_lt`, proved); what remains is the transfer to
  expansion coefficients (the `(1+u)^N` factors, as in `AssocCoeffRules.logCoeff_commutator_holds`).
* `HLZ544 P₁ P₂` (pure algebra in `P₁`, `P₂`): on a `τ`-stable space of bilinear functions all of
  whose elements are lower truncated and compatible, the associator formula holds.  Source:
  HLZ IV, Thm. 5.44 (proof in §6.1, formal calculus; with Thm. 5.45 for the stability).

`tauAssociator_of_compat : StronglyRational W → CoeffCompat W → (∀ irreducible P₁ P₂,
HLZ544 P₁ P₂) → TauAssociator W`, and `coeffWeakInput_of_compat`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorCompat

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable VOA.Huang.PzTensorBilin
open VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan VOA.Huang.PzTensorCommutator
open VOA.Huang.LogRemovalWeak
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
variable {P₁ P₂ : LWModule W}

/-- The local `w₂`-part of the compatibility identity, `Σ_j C(ℓ,j)(−1)^{ℓ−j} G(w₁, a_j w₂)`. -/
noncomputable def locR {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (ell : ℤ)
    (G : HomPair P₁ P₂ → ℂ) (x : HomPair P₁ P₂) : ℂ :=
  ∑ j ∈ Finset.range (PzTensorAction.lowBound P₂.h x.α₂ γ),
    cbz ell j * negOnePow (ell - j) * G (pairRight x ha j)

/-- **The `P(1)`-compatibility condition** for one function (all homogeneous states, all `ℓ`). -/
def CompatFn (G : HomPair P₁ P₂ → ℂ) : Prop :=
  ∀ (γ : ℤ) (a : 𝒱) (ha : a ∈ W.grading γ) (ell : ℤ), ∃ K : ℕ,
    (∀ k : ℕ, K ≤ k → copT ha (ell - k) G = 0) ∧
    ∀ x : HomPair P₁ P₂, G (pairLeft x ha ell) + locR ha ell G x
      = ∑ k ∈ Finset.range K, cbz ell k * negOnePow k * copT ha (ell - k) G x

/-- **`CoeffCompat`** (named; TRUE): every coefficient function of a product of intertwining
operators among irreducible modules of a strongly rational `V` satisfies the compatibility
condition.  Analytic input: the left and right associator identities (proved, values) and the
weight bound (proved); open: the transfer of the left associator to expansion coefficients. -/
def CoeffCompat (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∀ (α₃ h₄ : ℂ) (w₃ : P₃.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ),
    w₃ ∈ P₃.isMod.weight α₃ → SupportedAt P₄.isMod f h₄ →
  ∀ (n : ℂ) (k : ℕ), CompatFn (coefFun Y₁ Y₂ f w₃ α₃ h₄ n k)

/-- **`HLZ544`** (named; TRUE — Huang–Lepowsky–Zhang IV, Thm. 5.44 with Thm. 5.45, `z = 1`):
on a `τ`-stable space of bilinear functions whose elements are all lower truncated and
compatible, the associator formula for the `P(1)`-action holds.  Pure algebra in `P₁`, `P₂`. -/
def HLZ544 (P₁ P₂ : LWModule W) : Prop :=
  ∀ S : Submodule ℂ (HomPair P₁ P₂ → ℂ), S ≤ bilin P₁ P₂ →
    (∀ (β : ℤ) (u : 𝒱) (hu : u ∈ W.grading β) (m : ℤ) (G : HomPair P₁ P₂ → ℂ),
      G ∈ S → tauHom hu m G ∈ S) →
    (∀ G ∈ S, ∀ (γ : ℤ) (a : 𝒱) (ha : a ∈ W.grading γ),
      ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0) →
    (∀ G ∈ S, CompatFn G) →
  ∀ (β γ : ℤ) (u v : 𝒱) (hu : u ∈ W.grading β) (hv : v ∈ W.grading γ) (ell n : ℤ)
    (G : HomPair P₁ P₂ → ℂ), G ∈ S →
    (∑ᶠ i : ℤ, (negOnePow i * cbz ell i) •
        (tauHom hu (ell - i) (tauHom hv (n + i) G)
          - negOnePow ell • tauHom hv (ell + n - i) (tauHom hu i G)))
      = tauHom (W.smul_mem_grading hu hv ell) n G

/-! ## Closure of the compatibility condition under linear combinations -/

theorem locR_add {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (ell : ℤ) (G G' : HomPair P₁ P₂ → ℂ)
    (x : HomPair P₁ P₂) : locR ha ell (G + G') x = locR ha ell G x + locR ha ell G' x := by
  simp only [locR, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem locR_smul {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ) (ell : ℤ) (c : ℂ)
    (G : HomPair P₁ P₂ → ℂ) (x : HomPair P₁ P₂) :
    locR ha ell (c • G) x = c * locR ha ell G x := by
  simp only [locR, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem compatFn_zero : CompatFn (0 : HomPair P₁ P₂ → ℂ) := by
  intro γ a ha ell
  refine ⟨0, fun k _ => ?_, fun x => ?_⟩
  · funext x; simp [copT]
  · simp [locR]

theorem copT_eq_zero_of_le {G : HomPair P₁ P₂ → ℂ} {γ : ℤ} {a : 𝒱} (ha : a ∈ W.grading γ)
    {ell : ℤ} {K K' : ℕ} (hK : ∀ k : ℕ, K ≤ k → copT ha (ell - k) G = 0) (hKK' : K ≤ K') :
    ∑ k ∈ Finset.range K', cbz ell k * negOnePow k * copT ha (ell - k) G x
      = ∑ k ∈ Finset.range K, cbz ell k * negOnePow k * copT ha (ell - k) G x := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 hKK') fun k _ hk => ?_).symm
  rw [Finset.mem_range, not_lt] at hk
  rw [hK k hk, Pi.zero_apply, mul_zero]

theorem compatFn_add {G G' : HomPair P₁ P₂ → ℂ} (hG : CompatFn G) (hG' : CompatFn G') :
    CompatFn (G + G') := by
  intro γ a ha ell
  obtain ⟨K, hK, hid⟩ := hG γ a ha ell
  obtain ⟨K', hK', hid'⟩ := hG' γ a ha ell
  refine ⟨max K K', fun k hk => ?_, fun x => ?_⟩
  · funext x
    rw [copT_add, hK k (le_of_max_le_left hk), hK' k (le_of_max_le_right hk)]
    simp
  · simp only [Pi.add_apply, locR_add, copT_add, mul_add, Finset.sum_add_distrib]
    rw [copT_eq_zero_of_le ha hK (le_max_left K K'), copT_eq_zero_of_le ha hK' (le_max_right K K'),
      ← hid x, ← hid' x]
    ring

theorem compatFn_smul (c : ℂ) {G : HomPair P₁ P₂ → ℂ} (hG : CompatFn G) : CompatFn (c • G) := by
  intro γ a ha ell
  obtain ⟨K, hK, hid⟩ := hG γ a ha ell
  refine ⟨K, fun k hk => ?_, fun x => ?_⟩
  · funext x
    rw [copT_smul, hK k hk]
    simp
  · simp only [Pi.smul_apply, smul_eq_mul, locR_smul, copT_smul]
    rw [← mul_add, hid x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-! ## The reduction -/

section Reduction

variable {P₃ P₄ Q : LWModule W}
  (hV : StronglyRational W)
  (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)

include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂

/-- Lower truncation of the transposed coproduct on `Λ`. -/
theorem copT_truncation_coefSpan {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ coefSpan Y₁ Y₂) {γ : ℤ}
    {a : 𝒱} (ha : a ∈ W.grading γ) : ∃ P : ℤ, ∀ p : ℤ, p ≤ P → copT ha p G = 0 := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, w₃, α₃, h₄, n, k, h₃, hf, rfl⟩ := hG
    have hB := coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n k
    obtain ⟨P, hP⟩ := coproduct_lower_truncation hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf ha n k
    refine ⟨P, fun p hp => ?_⟩
    funext x
    obtain ⟨N₁, hN₁, hz⟩ := hP p hp x
    rw [copT_eq_sum hB ha p x hN₁, hz, Pi.zero_apply]
  | zero => exact ⟨0, fun p _ => by funext x; simp [copT]⟩
  | add G G' _ _ ih ih' =>
    obtain ⟨P, hP⟩ := ih
    obtain ⟨P', hP'⟩ := ih'
    refine ⟨min P P', fun p hp => ?_⟩
    funext x
    rw [copT_add, hP p (le_trans hp (min_le_left _ _)), hP' p (le_trans hp (min_le_right _ _))]
    simp
  | smul c G _ ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨P, fun p hp => ?_⟩
    funext x
    rw [copT_smul, hP p hp]
    simp

omit hV i₁ i₂ i₃ i₄ hY₁ hY₂ in
/-- The compatibility condition on `Λ` from `CoeffCompat`. -/
theorem compatFn_coefSpan (hC : CoeffCompat W)
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂) (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    {G : HomPair P₁ P₂ → ℂ} (hG : G ∈ coefSpan Y₁ Y₂) : CompatFn G := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, w₃, α₃, h₄, n, k, h₃, hf, rfl⟩ := hG
    exact hC P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ α₃ h₄ w₃ f h₃ hf n k
  | zero => exact compatFn_zero
  | add G G' _ _ ih ih' => exact compatFn_add ih ih'
  | smul c G _ ih => exact compatFn_smul c ih

end Reduction

/-- **`TauAssociator` from compatibility + HLZ Thm. 5.44.** -/
theorem tauAssociator_of_compat (hV : StronglyRational W) (hC : CoeffCompat W)
    (hH : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → HLZ544 P₁ P₂) :
    TauAssociator W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂ β γ u v hu hv ell n G hG
  exact hH P₁ P₂ i₁ i₂ (coefSpan Y₁ Y₂) (coefSpan_le_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂)
    (fun β u hu m G hG => tauHom_mem_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hG hu m)
    (fun G hG γ a ha => copT_truncation_coefSpan hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hG ha)
    (fun G hG => compatFn_coefSpan iQ hC hY₁ hY₂ i₁ i₂ i₃ i₄ hG)
    β γ u v hu hv ell n G hG

/-- **`CoeffWeakInput` from the two remaining named inputs.** -/
theorem coeffWeakInput_of_compat (hV : StronglyRational W) (hC : CoeffCompat W)
    (hH : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → HLZ544 P₁ P₂) :
    CoeffWeakInput W :=
  coeffWeakInput_of_tauAssociator hV (tauAssociator_of_compat hV hC hH)

/-- **`AssociativityInput` from the remaining named inputs.** -/
theorem associativityInput_of_compat (hV : StronglyRational W) (hABD : ABDWeakIsAdmissible W)
    (hC : CoeffCompat W)
    (hH : ∀ P₁ P₂ : LWModule W, P₁.IsIrreducibleLW → P₂.IsIrreducibleLW → HLZ544 P₁ P₂)
    (hZ : AssocCoeffIdentityZero W) : AssociativityInput W :=
  associativityInput_of_tauAssociator hV hABD (tauAssociator_of_compat hV hC hH) hZ

end VOA.Huang.PzTensorCompat
