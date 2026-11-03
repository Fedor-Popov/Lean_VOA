/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.PzTensorY4
import VOA.Huang.PzTensorCompatProof

/-!
# The outside Jacobi identity of the coefficient functions (part 1)

For fixed outside data `f ∈ P₄*` (supported at `h₄`), `w₃ ∈ P₃(α₃)`, a homogeneous state `u ∈ V_β`
and an intermediate weight `γ`, the coefficient functions `B_γ(f, w₃)` satisfy the **outside
Borcherds identity** (all `ℓ, m ∈ ℤ`):

`Σ_i (−1)^i C(ℓ,i) [B_γ(f∘u_{ℓ+m−i}, w₃) − (−1)^ℓ B_γ(f, u_{m+i}w₃)]
   = Σ_i C(m,i) Δᵀ(u_{ℓ+i}) B_{γ+β−ℓ−i−1}(f, w₃)`

(`outE_eq_zero`).  It is the Jacobi identity of the second iterate intertwiner `𝒴₃` paired with
`f`.  Proof: an abstract Pascal propagation (`outer_vanish`) from the two boundary families —
`m = 0` (the coproduct identity `AssocTauStable.coefFun_coproduct_holds`) and
`ℓ = 0` (the commutator identity `AssocCoeffRules.logCoeff_commutator_holds`).

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.PzTensorOutside

open VOA VOA.Huang.PzTensorRho
open scoped BigOperators

/-! ## The abstract Pascal propagation -/

section Abstract

variable (X Y Z : ℤ → ℂ)

/-- The outside Borcherds defect of three sequences. -/
noncomputable def OE (ℓ m : ℤ) : ℂ :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * X (ℓ + m - i)
    - negOnePow ℓ * ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * Y (m + i)
    - ∑ᶠ i : ℤ, cbz m i * Z (ℓ + i)

variable {X Y Z}

theorem OE_rec (hX : ∃ K : ℤ, ∀ k, k ≤ K → X k = 0) (hY : ∃ K : ℤ, ∀ k, K ≤ k → Y k = 0)
    (hZ : ∃ K : ℤ, ∀ k, K ≤ k → Z k = 0) (ℓ m : ℤ) :
    OE X Y Z ℓ (m + 1) = OE X Y Z (ℓ + 1) m + OE X Y Z ℓ m := by
  obtain ⟨KX, hKX⟩ := hX
  obtain ⟨KY, hKY⟩ := hY
  obtain ⟨KZ, hKZ⟩ := hZ
  -- finite supports
  have fX : ∀ (L c : ℤ), Function.HasFiniteSupport fun i : ℤ =>
      (negOnePow i * cbz L (i - c)) * X (L + m + 1 - i) := fun L c =>
    hfs_of _ c (max (L + m + 1 - KX) c) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg (by omega)]; ring
      · rw [hKX _ (by omega)]; ring
  have fY : ∀ (L c : ℤ), Function.HasFiniteSupport fun i : ℤ =>
      (negOnePow i * cbz L (i - c)) * Y (m + i) := fun L c =>
    hfs_of _ c (max (KY - m) c) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg (by omega)]; ring
      · rw [hKY _ (by omega)]; ring
  have fZ : ∀ (c : ℤ), Function.HasFiniteSupport fun i : ℤ => cbz m (i - c) * Z (ℓ + i) :=
    fun c => hfs_of _ c (max (KZ - ℓ) c) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg (by omega)]; ring
      · rw [hKZ _ (by omega)]; ring
  -- `X`-part
  have hXp : ∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) * X (ℓ + 1 + m - i)
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * X (ℓ + (m + 1) - i)
        - ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * X (ℓ + m - i) := by
    have e : ∀ i, (negOnePow i * cbz (ℓ + 1) i) * X (ℓ + 1 + m - i)
        = (negOnePow i * cbz ℓ (i - 0)) * X (ℓ + m + 1 - i)
          + (negOnePow i * cbz ℓ (i - 1)) * X (ℓ + m + 1 - i) := fun i => by
      rw [cbz_pascal_up, sub_zero, show ℓ + 1 + m - i = ℓ + m + 1 - i by ring]; ring
    rw [finsum_congr e, finsum_add_distrib (fX ℓ 0) (fX ℓ 1)]
    have e1 : ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 0)) * X (ℓ + m + 1 - i)
        = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * X (ℓ + (m + 1) - i) :=
      finsum_congr fun i => by rw [sub_zero, show ℓ + m + 1 - i = ℓ + (m + 1) - i by ring]
    have e2 : ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) * X (ℓ + m + 1 - i)
        = -∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * X (ℓ + m - i) := by
      rw [← finsum_shift _ 1, ← neg_one_mul, mul_finsum]
      refine finsum_congr fun i => ?_
      rw [show i + 1 - 1 = i by ring, show ℓ + m + 1 - (i + 1) = ℓ + m - i by ring,
        negOnePow_succ]; ring
    rw [e1, e2]; ring
  -- `Y`-part
  have hYp : negOnePow (ℓ + 1) * ∑ᶠ i : ℤ, (negOnePow i * cbz (ℓ + 1) i) * Y (m + i)
      = negOnePow ℓ * ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * Y (m + 1 + i)
        - negOnePow ℓ * ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * Y (m + i) := by
    have e : ∀ i, (negOnePow i * cbz (ℓ + 1) i) * Y (m + i)
        = (negOnePow i * cbz ℓ (i - 0)) * Y (m + i)
          + (negOnePow i * cbz ℓ (i - 1)) * Y (m + i) := fun i => by
      rw [cbz_pascal_up, sub_zero]; ring
    rw [finsum_congr e, finsum_add_distrib (fY ℓ 0) (fY ℓ 1)]
    have e1 : ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 0)) * Y (m + i)
        = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * Y (m + i) :=
      finsum_congr fun i => by rw [sub_zero]
    have e2 : ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ (i - 1)) * Y (m + i)
        = -∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) * Y (m + 1 + i) := by
      rw [← finsum_shift _ 1, ← neg_one_mul, mul_finsum]
      refine finsum_congr fun i => ?_
      rw [show i + 1 - 1 = i by ring, show m + (i + 1) = m + 1 + i by ring, negOnePow_succ]; ring
    rw [e1, e2, negOnePow_succ]; ring
  -- `Z`-part
  have hZp : ∑ᶠ i : ℤ, cbz (m + 1) i * Z (ℓ + i)
      = ∑ᶠ i : ℤ, cbz m i * Z (ℓ + i) + ∑ᶠ i : ℤ, cbz m i * Z (ℓ + 1 + i) := by
    have e : ∀ i, cbz (m + 1) i * Z (ℓ + i) = cbz m (i - 0) * Z (ℓ + i)
        + cbz m (i - 1) * Z (ℓ + i) := fun i => by rw [cbz_pascal_up, sub_zero]; ring
    rw [finsum_congr e, finsum_add_distrib (fZ 0) (fZ 1)]
    have e1 : ∑ᶠ i : ℤ, cbz m (i - 0) * Z (ℓ + i) = ∑ᶠ i : ℤ, cbz m i * Z (ℓ + i) :=
      finsum_congr fun i => by rw [sub_zero]
    have e2 : ∑ᶠ i : ℤ, cbz m (i - 1) * Z (ℓ + i) = ∑ᶠ i : ℤ, cbz m i * Z (ℓ + 1 + i) := by
      rw [← finsum_shift _ 1]
      exact finsum_congr fun i => by rw [show i + 1 - 1 = i by ring,
        show ℓ + (i + 1) = ℓ + 1 + i by ring]
    rw [e1, e2]
  unfold OE
  linear_combination (-1 : ℂ) * hXp + hYp - hZp

/-- **Outside Pascal propagation**: the defect vanishes identically once it vanishes on the two
boundary lines `m = 0` and `ℓ = 0`. -/
theorem outer_vanish (hX : ∃ K : ℤ, ∀ k, k ≤ K → X k = 0) (hY : ∃ K : ℤ, ∀ k, K ≤ k → Y k = 0)
    (hZ : ∃ K : ℤ, ∀ k, K ≤ k → Z k = 0) (hm0 : ∀ ℓ, OE X Y Z ℓ 0 = 0)
    (hl0 : ∀ m, OE X Y Z 0 m = 0) (ℓ m : ℤ) : OE X Y Z ℓ m = 0 :=
  pascal_vanish (fun m ℓ => OE X Y Z ℓ m) (fun m ℓ => OE_rec hX hY hZ ℓ m) hm0 hl0 m ℓ

end Abstract

/-! ## The commutator identity with an explicit truncation bound -/

section Coef

open VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget VOA.Huang.AssocExpansion
open VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction VOA.Huang.AssocCoeffRules
open VOA.Huang.AssocCommutator VOA.Huang.LogRemovalSemisimple VOA.Huang.AssocTauStable
open VOA.Huang.PzTensorBilin VOA.Huang.PzTensorAction VOA.Huang.PzTensorSpan
open VOA.Huang.PzTensorHatBridge
open VOA.Huang.FrobeniusLog (psEval)

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- `logCoeff_commutator_holds` with the truncation bound `N` supplied by the caller. -/
theorem logCoeff_commutator_N (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {v : 𝒱} (hv : v ∈ W.grading β) (m : ℤ) {N : ℤ}
    (hN₁ : ∀ i, N ≤ i → mode (P₁.isMod.YM v) i w₁ = 0)
    (hN₂ : ∀ i, N ≤ i → mode (P₂.isMod.YM v) i w₂ = 0) (μ : ℂ) (k : ℕ) :
    logCoeff overlapDomain (prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h)) μ k
      = logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃)
          (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1) (α₂ + α₃ - 1 - Q.h)) μ k
        + ∑ i ∈ Finset.Ico 0 N, cbz m i * ∑ᶠ j : ℕ, PowerSeries.coeff j (binPS (m - i))
            * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ)) (α₂ + α₃ - 1 - Q.h)) (μ - j) k
        + ∑ i ∈ Finset.Ico 0 N, cbz m i
            * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃
                (α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 + (m - i : ℤ))
                (α₂ + α₃ - 1 - Q.h + (m - i : ℤ))) μ k := by
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  set S := α₁ + α₂ + α₃ - h₄ - 2 + β - m - 1 with hSdef
  set ν := α₂ + α₃ - 1 - Q.h with hνdef
  have hN : ∀ t ∈ overlapDomain,
      prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃ S ν t
        = prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃) S ν t
          + ∑ i ∈ Finset.Ico 0 N, cbz m i * (psEval (binPS (m - i)) (Complex.exp t)
              * prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃ (S + (m - i : ℤ)) ν t)
          + ∑ i ∈ Finset.Ico 0 N, cbz m i
              * prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃ (S + (m - i : ℤ))
                  (ν + (m - i : ℤ)) t := by
    intro t ht
    have hz₂ : (1 : ℂ) ≠ 0 := one_ne_zero
    have hz : ‖(1 : ℂ)‖ < ‖1 + Complex.exp t‖ := by rw [norm_one]; exact one_lt_norm ht
    have hz₁ : 1 + Complex.exp t ≠ 0 := one_add_exp_ne_zero ht
    have key := prodValueZ_commutator hY₁ hY₂ v m f w₁ w₂ w₃ hN₁ hN₂ S ν hz₁ hz₂
      (summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂
        (VOA.mode_mem_weight P₃.isMod hv h₃ m) hf (by rw [hSdef]; ring) (m + 1 - β)
        (by rw [hνdef]; push_cast; ring) hz₂ hz)
      (fun i _ => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂
        (VOA.mode_mem_weight P₁.isMod hv h₁ i) h₂ h₃ hf (by rw [hSdef]; push_cast; ring) 0
        (by rw [hνdef]; push_cast; ring) hz₂ hz)
      (fun i _ => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁
        (VOA.mode_mem_weight P₂.isMod hv h₂ i) h₃ hf (by rw [hSdef]; push_cast; ring)
        (m + 1 - β) (by rw [hνdef]; push_cast; ring) hz₂ hz)
    unfold prodFunZ
    rw [key]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [psEval_binPS _ (norm_exp_lt_one ht), Complex.cpow_intCast]
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.one_cpow, mul_one]
  set F₃ := prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM v) m w₃) S ν with hF₃
  set F₁ : ℤ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM v) i w₁) w₂ w₃
    (S + (m - i : ℤ)) ν with hF₁
  set F₂ : ℤ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM v) i w₂) w₃
    (S + (m - i : ℤ)) (ν + (m - i : ℤ)) with hF₂
  have e₃ : HasLogExp overlapDomain F₃ :=
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hv h₃ m) hf (by rw [hSdef]; ring) (m + 1 - β)
      (by rw [hνdef]; push_cast; ring)
  have e₁ : ∀ i, HasLogExp overlapDomain (F₁ i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
      (VOA.mode_mem_weight P₁.isMod hv h₁ i) h₂ h₃ hf (by rw [hSdef]; push_cast; ring) 0
      (by rw [hνdef]; push_cast; ring)
  have e₂ : ∀ i, HasLogExp overlapDomain (F₂ i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁
      (VOA.mode_mem_weight P₂.isMod hv h₂ i) h₃ hf (by rw [hSdef]; push_cast; ring) (m + 1 - β)
      (by rw [hνdef]; push_cast; ring)
  have e₁' : ∀ i, HasLogExp overlapDomain
      (fun t => cbz m i * (psEval (binPS (m - i)) (Complex.exp t) * F₁ i t)) := fun i =>
    hasLogExp_smul _ (hasLogExp_psEval_mul hs (e₁ i) (binPS_mem _))
  have e₂' : ∀ i, HasLogExp overlapDomain (fun t => cbz m i * F₂ i t) := fun i =>
    hasLogExp_smul _ (e₂ i)
  have eS₁ := hasLogExp_sum (Finset.Ico 0 N) (fun i _ => e₁' i)
  have eS₂ := hasLogExp_sum (Finset.Ico 0 N) (fun i _ => e₂' i)
  have hsum : ∀ t ∈ overlapDomain,
      prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM v) m) w₁ w₂ w₃ S ν t
        = ((F₃ + fun t => ∑ i ∈ Finset.Ico 0 N,
              cbz m i * (psEval (binPS (m - i)) (Complex.exp t) * F₁ i t))
          + fun t => ∑ i ∈ Finset.Ico 0 N, cbz m i * F₂ i t) t := fun t ht => hN t ht
  have eA := hasLogExp_add e₃ eS₁
  rw [logCoeff_congr hU hs hne hsum (hasLogExp_congr (fun t ht => (hsum t ht).symm)
      (hasLogExp_add eA eS₂)),
    logCoeff_add hU hs hne eA eS₂, logCoeff_add hU hs hne e₃ eS₁,
    logCoeff_sum hU hs hne _ (fun i _ => e₁' i), logCoeff_sum hU hs hne _ (fun i _ => e₂' i)]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_psEval_mul hs (e₁ i) (binPS_mem _)),
      logCoeff_psEval_mul hU hs hne (e₁ i) (binPS_mem _)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [logCoeff_smul hU hs hne _ (e₂ i)]

/-- A finsum over `ℤ` of a family vanishing on negatives is the finsum over `ℕ`. -/
theorem finsum_int_eq_nat {X : Type*} [AddCommMonoid X] (g : ℤ → X) (h : ∀ j, j < 0 → g j = 0) :
    ∑ᶠ j : ℤ, g j = ∑ᶠ j : ℕ, g (j : ℤ) := by
  have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := Nat.cast_injective
  rw [← finsum_mem_range hinj (f := g)]
  have hsub : Function.support g ⊆ Set.range (fun j : ℕ => (j : ℤ)) := by
    intro j hj
    rw [Function.mem_support] at hj
    have : 0 ≤ j := by by_contra hc; exact hj (h j (by omega))
    exact ⟨j.toNat, by simp [Int.toNat_of_nonneg this]⟩
  rw [← finsum_mem_inter_support g (Set.range (fun j : ℕ => (j : ℤ))),
    ← finsum_mem_univ (f := g), ← finsum_mem_inter_support g Set.univ, Set.univ_inter,
    Set.inter_eq_right.mpr hsub]

section Commutator

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
  {wt : ℤ} {u : 𝒱} (hu : u ∈ W.grading wt)
include hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hu

/-- **The commutator identity on the coefficient functions**:
`B_γ(f∘u_m, w₃) − B_γ(f, u_m w₃) = Σ_i C(m,i) Δᵀ(u_i) B_{γ+β−i−1}(f, w₃)`. -/
theorem coefFun_commutator (m : ℤ) (x : HomPair P₁ P₂) (γ : ℂ) (kk : ℕ) :
    coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) m) w₃ α₃ (h₄ - wt + m + 1) γ kk x
      - coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) m w₃) (α₃ + wt - m - 1) h₄ γ kk x
      = ∑ᶠ i : ℤ, cbz m i * copT hu i (coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk) x := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_truncation P₁.isMod u x.w₁
  obtain ⟨N₂, hN₂⟩ := exists_nat_truncation P₂.isMod u x.w₂
  set N : ℕ := max N₁ N₂ with hNdef
  have hN₁' : ∀ i : ℤ, (N : ℤ) ≤ i → mode (P₁.isMod.YM u) i x.w₁ = 0 := fun i hi => by
    have := hN₁ i.toNat (by omega); rwa [Int.toNat_of_nonneg (by omega)] at this
  have hN₂' : ∀ i : ℤ, (N : ℤ) ≤ i → mode (P₂.isMod.YM u) i x.w₂ = 0 := fun i hi => by
    have := hN₂ i.toNat (by omega); rwa [Int.toNat_of_nonneg (by omega)] at this
  set μ : ℂ := γ - x.α₁ - x.α₂ with hμ
  have hc := logCoeff_commutator_N hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ x.h₁ x.h₂ h₃ hf hu m hN₁' hN₂' μ kk
  set S : ℂ := x.α₁ + x.α₂ + α₃ - h₄ - 2 + wt - m - 1 with hS
  set ν : ℂ := x.α₂ + α₃ - 1 - Q.h with hν
  -- identify the two outside terms
  have eX : coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) m) w₃ α₃ (h₄ - wt + m + 1) γ kk x
      = logCoeff overlapDomain (prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) m) x.w₁ x.w₂ w₃ S ν)
          μ kk := by
    simp only [coefFun, prodExpCoeff]
    rw [prodFunZ_canonical hY₂ _ x.w₁ x.h₂ h₃ S 0 ν (by rw [hν]; push_cast; ring)]
    congr 2; rw [hS]; ring
  have eY : coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) m w₃) (α₃ + wt - m - 1) h₄ γ kk x
      = logCoeff overlapDomain (prodFunZ Y₁ Y₂ f x.w₁ x.w₂ (mode (P₃.isMod.YM u) m w₃) S ν)
          μ kk := by
    simp only [coefFun, prodExpCoeff]
    rw [prodFunZ_canonical hY₂ _ x.w₁ x.h₂ (VOA.mode_mem_weight P₃.isMod hu h₃ m) S
      (m + 1 - wt) ν (by rw [hν]; push_cast; ring)]
    congr 2
    rw [hS]; ring
  -- the `w₂`-terms
  have eR : ∀ i : ℤ, coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairRight x hu i)
      = logCoeff overlapDomain (prodFunZ Y₁ Y₂ f x.w₁ (mode (P₂.isMod.YM u) i x.w₂) w₃
          (S + (m - i : ℤ)) (ν + (m - i : ℤ))) μ kk := by
    intro i
    simp only [coefFun, prodExpCoeff, pairRight]
    rw [prodFunZ_canonical hY₂ _ x.w₁ (VOA.mode_mem_weight P₂.isMod hu x.h₂ i) h₃ _
      (m + 1 - wt) _ (by rw [hν]; push_cast; ring)]
    rw [show x.α₁ + (x.α₂ + (wt : ℂ) - (i : ℂ) - 1) + α₃ - h₄ - 2 = S + ((m - i : ℤ) : ℂ) by
        rw [hS]; push_cast; ring,
      show γ + (wt : ℂ) - (i : ℂ) - 1 - x.α₁ - (x.α₂ + (wt : ℂ) - (i : ℂ) - 1) = μ by
        rw [hμ]; ring]
  -- the `w₁`-terms
  have eL : ∀ (i r : ℤ), coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairLeft x hu r)
      = logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
          (S + (m - r : ℤ)) ν) (μ - ((i - r : ℤ) : ℂ)) kk := by
    intro i r
    simp only [coefFun, prodExpCoeff, pairLeft]
    rw [prodFunZ_canonical hY₂ _ _ x.h₂ h₃ _ 0 ν (by rw [hν]; push_cast; ring)]
    rw [show x.α₁ + (wt : ℂ) - (r : ℂ) - 1 + x.α₂ + α₃ - h₄ - 2 = S + ((m - r : ℤ) : ℂ) by
        rw [hS]; push_cast; ring,
      show γ + (wt : ℂ) - (i : ℂ) - 1 - (x.α₁ + (wt : ℂ) - (r : ℂ) - 1) - x.α₂
        = μ - ((i - r : ℤ) : ℂ) by rw [hμ]; push_cast; ring]
  -- vanishing facts
  obtain ⟨M, hM⟩ := VOA.Huang.LogRemovalWeightBound.coefFun_eq_zero_of_re_lt hV i₁ i₂ i₃ i₄ iQ
    hY₁ hY₂
  obtain ⟨IL, hIL⟩ := exists_int_gt (γ.re + wt - 1 - (M - α₃.re - h₄.re))
  have hBz : ∀ i : ℤ, IL ≤ i → coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk = 0 := by
    intro i hi
    refine hM α₃ h₄ w₃ f h₃ hf _ kk ?_
    have : (IL : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
    linarith
  have hL0 : ∀ (r : ℤ), (N : ℤ) ≤ r → ∀ μ' : ℂ,
      logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
        (S + (m - r : ℤ)) ν) μ' kk = 0 := by
    intro r hr μ'
    rw [hN₁' r hr]
    unfold prodFunZ
    have : (fun t : ℂ => prodValueZ Y₁ Y₂ f 0 x.w₂ w₃ (S + (m - r : ℤ)) ν (1 + Complex.exp t) 1)
        = fun _ => 0 := by
      funext t; unfold prodValueZ; simp [prodTermZ, prodCoeff]
    rw [this]
    exact logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty _ _
  have hBil : ∀ n : ℂ, coefFun Y₁ Y₂ f w₃ α₃ h₄ n kk ∈ bilin P₁ P₂ := fun n =>
    coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf n kk
  rw [eX, eY, hc]
  -- expand the right-hand side
  have hcopT : ∀ i : ℤ, copT hu i (coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk) x
      = coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairRight x hu i)
        + ∑ᶠ r : ℤ, cbz i r * coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairLeft x hu r) := by
    intro i
    rw [copT_eq_sum (hBil _) hu i x hN₁, PzTensorHatBridge.finsum_int_eq_range
      (fun r : ℤ => cbz i r * coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairLeft x hu r))
      N₁ (fun r hr => by
      dsimp only
      rcases hr with hr | hr
      · rw [cbz_neg hr]; ring
      · have h0 : mode (P₁.isMod.YM u) r x.w₁ = 0 := by
          have := hN₁ r.toNat (by omega); rwa [Int.toNat_of_nonneg (by omega)] at this
        rw [coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inl h0), mul_zero])]
  simp only [hcopT, mul_add]
  have fR : Function.HasFiniteSupport fun i : ℤ =>
      cbz m i * coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairRight x hu i) :=
    hfs_of _ 0 N fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inl (hN₂' i (by omega)))),
          mul_zero]
  have fL : Function.HasFiniteSupport fun i : ℤ =>
      cbz m i * ∑ᶠ r : ℤ, cbz i r
        * coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairLeft x hu r) :=
    hfs_of _ 0 (max IL 0) fun i hi => by
      rcases hi with hi | hi
      · rw [cbz_neg hi]; ring
      · rw [hBz i (by omega)]; simp
  rw [finsum_add_distrib fR fL]
  -- the `w₂`-part
  have hRpart : ∑ᶠ i : ℤ, cbz m i
        * coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairRight x hu i)
      = ∑ i ∈ Finset.Ico 0 (N : ℤ), cbz m i
          * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f x.w₁ (mode (P₂.isMod.YM u) i x.w₂) w₃
              (S + (m - i : ℤ)) (ν + (m - i : ℤ))) μ kk := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ico 0 (N : ℤ)) (fun i hi => by
      rw [Function.mem_support] at hi
      simp only [Finset.coe_Ico, Set.mem_Ico]
      by_contra hc'
      apply hi
      rcases lt_or_ge i 0 with h0 | h0
      · rw [cbz_neg h0]; ring
      · rw [coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inl (hN₂' i (by omega)))),
          mul_zero])]
    exact Finset.sum_congr rfl fun i _ => by rw [eR]
  -- the `w₁`-part
  set g : ℤ → ℂ := fun r => cbz m r * ∑ᶠ j : ℕ, cbz (m - r) j
    * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
        (S + (m - r : ℤ)) ν) (μ - j) kk with hg
  have hA : ∑ i ∈ Finset.Ico 0 (N : ℤ), cbz m i * ∑ᶠ j : ℕ, PowerSeries.coeff j (binPS (m - i))
        * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) i x.w₁) x.w₂ w₃
            (S + (m - i : ℤ)) ν) (μ - j) kk
      = ∑ᶠ r : ℤ, g r := by
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Ico 0 (N : ℤ)) (fun r hr => by
      rw [Function.mem_support] at hr
      simp only [Finset.coe_Ico, Set.mem_Ico]
      by_contra hc'
      apply hr
      simp only [hg]
      rcases lt_or_ge r 0 with h0 | h0
      · rw [cbz_neg h0]; ring
      · rw [finsum_eq_zero_of_forall_eq_zero fun j => by rw [hL0 r (by omega)]; ring]; ring)]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hg]
    congr 1
    exact finsum_congr fun j => by rw [VOA.Huang.PzTensorCompatProof.coeff_binPS]
  have hLpart : ∑ᶠ i : ℤ, cbz m i * ∑ᶠ r : ℤ, cbz i r
        * coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - i - 1) kk (pairLeft x hu r)
      = ∑ᶠ r : ℤ, g r := by
    simp only [mul_finsum]
    rw [finsum_comm_box _ 0 (max IL 0) 0 N (fun i r hir => by
      rcases hir with h | h | h | h
      · rw [cbz_neg h]; ring
      · rw [hBz i (by omega)]; simp
      · rw [cbz_neg h]; ring
      · rw [coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inl (hN₁' r (by omega)))]; ring)]
    refine finsum_congr fun r => ?_
    simp only [hg]
    rcases lt_or_ge r 0 with h0 | h0
    · rw [cbz_neg h0, zero_mul]
      exact finsum_eq_zero_of_forall_eq_zero fun i => by rw [cbz_neg h0]; ring
    rw [← finsum_shift _ r, finsum_int_eq_nat _ (fun j hj => by
      rcases lt_or_ge (j + r) 0 with h1 | h1
      · rw [cbz_neg h1]; ring
      · rw [cbz_nat_lt h1 (by omega)]; ring), mul_finsum]
    refine finsum_congr fun j => ?_
    rw [eL, show ((j : ℤ) + r - r : ℤ) = (j : ℤ) by ring]
    have ht := trinom m (show 0 ≤ (j : ℤ) + r by omega) r
    rw [show (j : ℤ) + r - r = j by ring] at ht
    simp only [Int.cast_natCast]
    linear_combination (logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁)
        x.w₂ w₃ (S + (m - r : ℤ)) ν) (μ - j) kk) * ht.symm
  rw [hRpart, hLpart, ← hA]
  ring

/-- **The outside Borcherds identity of the coefficient functions** (all `ℓ, m`). -/
theorem outE_eq_zero (γ : ℂ) (kk : ℕ) (x : HomPair P₁ P₂) (ℓ m : ℤ) :
    OE (fun k => coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) k) w₃ α₃ (h₄ - wt + k + 1) γ kk x)
      (fun k => coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) k w₃) (α₃ + wt - k - 1) h₄ γ kk x)
      (fun k => copT hu k (coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - k - 1) kk) x) ℓ m = 0 := by
  refine outer_vanish ?_ ?_ ?_ ?_ ?_ ℓ m
  · obtain ⟨K, hK⟩ := exists_int_lt (P₄.h.re - h₄.re + wt - 1)
    refine ⟨K, fun k hk => ?_⟩
    have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
    have h0 : f ∘ₗ mode (P₄.isMod.YM u) k = 0 :=
      comp_mode_eq_zero_of_lt P₄.isLow hf hu (by
        simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re]
        linarith)
    exact coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inr h0)))
  · obtain ⟨N, hN⟩ := P₃.isMod.truncation u w₃
    exact ⟨N, fun k hk => coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inl (hN k hk))))⟩
  · obtain ⟨M, hM⟩ := VOA.Huang.LogRemovalWeightBound.coefFun_eq_zero_of_re_lt hV i₁ i₂ i₃ i₄ iQ
      hY₁ hY₂
    obtain ⟨K, hK⟩ := exists_int_gt (γ.re + wt - 1 - (M - α₃.re - h₄.re))
    refine ⟨K, fun k hk => ?_⟩
    have hk' : (K : ℝ) ≤ k := by exact_mod_cast hk
    rw [hM α₃ h₄ w₃ f h₃ hf _ kk (by
      simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, Complex.one_re]
      linarith)]
    simp [copT]
  · intro ℓ
    unfold OE
    beta_reduce
    have hZ0 : ∑ᶠ i : ℤ, cbz 0 i * copT hu (ℓ + i)
          (coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - ((ℓ + i : ℤ) : ℂ) - 1) kk) x
        = copT hu ℓ (coefFun Y₁ Y₂ f w₃ α₃ h₄ (γ + wt - ℓ - 1) kk) x := by
      rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_mul])]
      simp
    rw [hZ0]
    simp only [add_zero, zero_add]
    obtain ⟨NA, hNA⟩ := exists_comp_mode_vanish P₄.isLow hf hu ℓ
    obtain ⟨N₁, hN₁⟩ := exists_nat_truncation P₁.isMod u x.w₁
    obtain ⟨N₃, hN₃⟩ := exists_nat_truncation P₃.isMod u w₃
    have hcop := coefFun_coproduct_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hu ℓ x hNA hN₁ hN₃
      (γ + wt - ℓ - 1) kk
    rw [← copT_eq_sum (coefFun_mem_bilin hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf _ kk) hu ℓ x hN₁,
      show γ + (wt : ℂ) - ℓ - 1 - wt + ℓ + 1 = γ by ring] at hcop
    rw [hcop]
    rw [PzTensorHatBridge.finsum_int_eq_range (fun i : ℤ => (negOnePow i * cbz ℓ i)
        * coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (ℓ - i)) w₃ α₃ (h₄ - wt + ((ℓ - i : ℤ) : ℂ) + 1)
          γ kk x) NA (fun i hi => by
        dsimp only
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · have := hNA i.toNat (by omega)
          rw [Int.toNat_of_nonneg (by omega)] at this
          rw [coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inr this)))]; ring),
      PzTensorHatBridge.finsum_int_eq_range (fun i : ℤ => (negOnePow i * cbz ℓ i)
        * coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) i w₃) (α₃ + wt - (i : ℂ) - 1) h₄ γ kk x) N₃
        (fun i hi => by
        dsimp only
        rcases hi with hi | hi
        · rw [cbz_neg hi]; ring
        · have := hN₃ i.toNat (by omega)
          rw [Int.toNat_of_nonneg (by omega)] at this
          rw [coefFun_eq_zero_of _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inl this)))]; ring)]
    simp only [Int.cast_natCast]
    ring
  · intro m
    unfold OE
    beta_reduce
    have hX0 : ∑ᶠ i : ℤ, (negOnePow i * cbz 0 i)
          * coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (0 + m - i)) w₃ α₃
            (h₄ - wt + ((0 + m - i : ℤ) : ℂ) + 1) γ kk x
        = coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) m) w₃ α₃ (h₄ - wt + m + 1) γ kk x := by
      rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi]; ring)]
      simp [negOnePow]
    have hY0 : ∑ᶠ i : ℤ, (negOnePow i * cbz 0 i)
          * coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) (m + i) w₃) (α₃ + wt - ((m + i : ℤ) : ℂ) - 1)
            h₄ γ kk x
        = coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) m w₃) (α₃ + wt - m - 1) h₄ γ kk x := by
      rw [finsum_eq_single _ 0 (fun i hi => by rw [cbz_zero_left, if_neg hi]; ring)]
      simp [negOnePow]
    rw [hX0, hY0, show negOnePow 0 = 1 by simp [negOnePow], one_mul,
      coefFun_commutator hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hu m x γ kk]
    simp only [zero_add, sub_self]

end Commutator

end Coef

end VOA.Huang.PzTensorOutside
