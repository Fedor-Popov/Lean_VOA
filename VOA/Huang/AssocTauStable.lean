/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.AssocAssociator
import VOA.Huang.LogRemovalWeightBound

/-!
# The coproduct of a mode on the coefficient functionals is an outside action

For homogeneous `u ∈ V_β` and `p ∈ ℤ`, the transposed coproduct of the mode `u_p` at `P(1)`,
`Δᵀ(u_p) G (w₁, w₂) = G(w₁, u_p w₂) + Σᵢ C(p,i) G(uᵢ w₁, w₂)`
(the building block of the Huang–Lepowsky `P(1)`-action `τ` on functionals of `P₁ ⊗ P₂`), maps
every coefficient function `B_{n,k}(f, w₃)` of a product to a **finite combination of coefficient
functions with modified outside data** and the **same log index `k`**:

`Δᵀ(u_p) B_{n,k}(f, w₃) = Σᵢ (−1)ⁱ C(p,i) B_{n',k}(f∘u_{p−i}, w₃)
   − (−1)^p Σᵢ (−1)ⁱ C(p,i) B_{n',k}(f, uᵢ w₃)`, `n' = n + β − p − 1`

(`coefFun_coproduct_holds`).  The inside–inside terms of the right associator identity
(`AssocAssociator.prodValueZ_assoc_right`), `C(p,r) u^{p−r} F(u_r w₁, w₂)`, cancel the coproduct
terms exactly — this is where `(z₁ − z₂)^{p−r} = u^{p−r}` *preserves the intermediate weight*.
Consequences: the span of the coefficient functions is stable under every `Δᵀ(u_p)`, hence under
the `P(1)`-action (a finite combination of them, FHL (5.2.4)); the log index is preserved.

## Main results
* `supportedAt_comp_mode`, `comp_mode_eq_zero_of_lt`.
* `prodFunZ_assoc_right_holds` (function identity, all summability discharged).
* `logCoeff_assoc_right_holds`, `coefFun_coproduct_holds`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.AssocTauStable

open VOA VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.AssocCommutator VOA.Huang.AssocAssociator
open VOA.Huang.LogRemovalSemisimple VOA.Huang.LogRemovalBound
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## Functionals composed with modes -/

section Supp

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- `f ∘ u_q` is supported at `h − β + q + 1` if `f` is supported at `h` and `u ∈ V_β`. -/
theorem supportedAt_comp_mode {A : OrdVModule W M} {f : M →ₗ[ℂ] ℂ} {h : ℂ}
    (hf : SupportedAt A f h) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (q : ℤ) :
    SupportedAt A (f ∘ₗ mode (A.YM u) q) (h - β + q + 1) := by
  intro α hα x hx
  simp only [LinearMap.comp_apply]
  refine hf _ (fun he => hα ?_) _ (VOA.mode_mem_weight A hu hx q)
  linear_combination he

/-- `f ∘ u_q = 0` once the weight `h − β + q + 1` is below the lowest weight. -/
theorem comp_mode_eq_zero_of_lt {A : OrdVModule W M} {f : M →ₗ[ℂ] ℂ} {h h₀ : ℂ}
    (hl : IsLowestWeight A h₀) (hf : SupportedAt A f h) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β)
    {q : ℤ} (hq : (h - β + q + 1).re < h₀.re) : f ∘ₗ mode (A.YM u) q = 0 := by
  refine eq_zero_of_supportedAt_bot (supportedAt_comp_mode hf hu q) ?_
  by_contra hne
  obtain ⟨n, hn⟩ := hl _ hne
  rw [hn, Complex.add_re, Complex.natCast_re] at hq
  have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- A uniform index past which all `f ∘ u_{p−i}` vanish. -/
theorem exists_comp_mode_vanish {A : OrdVModule W M} {f : M →ₗ[ℂ] ℂ} {h h₀ : ℂ}
    (hl : IsLowestWeight A h₀) (hf : SupportedAt A f h) {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β)
    (p : ℤ) : ∃ NA : ℕ, ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (A.YM u) (p - i) = 0 := by
  obtain ⟨NA, hNA⟩ := exists_nat_gt ((h - β + p + 1).re - h₀.re)
  refine ⟨NA, fun i hi => comp_mode_eq_zero_of_lt hl hf hu ?_⟩
  have : (NA : ℝ) ≤ i := by exact_mod_cast hi
  simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re] at hNA ⊢
  push_cast
  linarith

/-- A truncation bound in `ℕ`. -/
theorem exists_nat_truncation (A : OrdVModule W M) (u : 𝒱) (x : M) :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i → mode (A.YM u) i x = 0 := by
  obtain ⟨N, hN⟩ := A.truncation u x
  exact ⟨N.toNat, fun i hi => hN i (by omega)⟩

end Supp

/-! ## The right associator identity on functions -/

section Holds

variable (hV : StronglyRational W)
  {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
  (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
  {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
  {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
  (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
  (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
  {α₁ α₂ α₃ h₄ : ℂ} {w₁ : P₁.carrier} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
  {f : P₄.carrier →ₗ[ℂ] ℂ}
  (h₁ : w₁ ∈ P₁.isMod.weight α₁) (h₂ : w₂ ∈ P₂.isMod.weight α₂)
  (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
  {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β)
include hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf hu

/-- **The right associator identity at `z₂ = 1`, `z₁ = 1 + e^t`** (functions on the overlap
domain), all summability discharged:
`F(w₁, u_p w₂) = Σᵢ (−1)ⁱC(p,i) F(f∘u_{p−i}) − (−1)^p Σᵢ (−1)ⁱC(p,i) F(uᵢw₃)
  − Σᵣ C(p,r) e^{(p−r)t} F(u_r w₁)`. -/
theorem prodFunZ_assoc_right_holds (p : ℤ) {NA N₁ N₃ : ℕ}
    (hNA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (p - i) = 0)
    (hN₁ : ∀ r : ℕ, N₁ ≤ r → mode (P₁.isMod.YM u) r w₁ = 0)
    (hN₃ : ∀ i : ℕ, N₃ ≤ i → mode (P₃.isMod.YM u) i w₃ = 0) :
    ∀ t ∈ overlapDomain,
    prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM u) p w₂) w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1) (α₂ + α₃ - 1 - Q.h) t
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz p i
          * prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (p - i)) w₁ w₂ w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 + ((i : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h + ((i : ℤ) : ℂ)) t
        - negOnePow p * ∑ i ∈ Finset.range N₃, negOnePow i * cbz p i
          * prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM u) i w₃)
              (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 + ((p - i : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h + ((p - i : ℤ) : ℂ)) t
        - ∑ r ∈ Finset.range N₁, cbz p r * Complex.exp (((p - r : ℤ) : ℂ) * t)
          * prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r w₁) w₂ w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 + ((p - r : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h) t := by
  intro t ht
  have hz : 1 < ‖1 + Complex.exp t‖ := one_lt_norm ht
  have hz₂ : (1 : ℂ) ≠ 0 := one_ne_zero
  have hz' : ‖(1 : ℂ)‖ < ‖1 + Complex.exp t‖ := by rw [norm_one]; exact hz
  unfold prodFunZ
  rw [prodValueZ_assoc_right hY₁ hY₂ u p f w₁ w₂ w₃ hNA hN₁ hN₃ _ _ _ hz
    (fun i => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃
      (supportedAt_comp_mode hf hu (p - i)) (by push_cast; ring) i (by push_cast; ring) hz₂ hz')
    (fun i => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hu h₃ i) hf (by push_cast; ring) (p + 1 - β)
      (by push_cast; ring) hz₂ hz')
    (fun r => summable_prodTermZ_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂
      (VOA.mode_mem_weight P₁.isMod hu h₁ r) h₂ h₃ hf (by push_cast; ring) 0
      (by push_cast; ring) hz₂ hz')]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [add_sub_cancel_left, ← Complex.exp_int_mul]

/-- **The right associator identity on expansion coefficients** at the iterate point. -/
theorem logCoeff_assoc_right_holds (iQ : Q.IsIrreducibleLW) (p : ℤ) {NA N₁ N₃ : ℕ}
    (hNA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (p - i) = 0)
    (hN₁ : ∀ r : ℕ, N₁ ≤ r → mode (P₁.isMod.YM u) r w₁ = 0)
    (hN₃ : ∀ i : ℕ, N₃ ≤ i → mode (P₃.isMod.YM u) i w₃ = 0) :
    ∀ (μ : ℂ) (k : ℕ),
    logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM u) p w₂) w₃
        (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1) (α₂ + α₃ - 1 - Q.h)) μ k
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz p i
          * logCoeff overlapDomain (prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (p - i)) w₁ w₂ w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 + ((i : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h + ((i : ℤ) : ℂ))) μ k
        - negOnePow p * ∑ i ∈ Finset.range N₃, negOnePow i * cbz p i
          * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM u) i w₃)
              (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 + ((p - i : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h + ((p - i : ℤ) : ℂ))) μ k
        - ∑ r ∈ Finset.range N₁, cbz p r
          * logCoeff overlapDomain (prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r w₁) w₂ w₃
              (α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 + ((p - r : ℤ) : ℂ))
              (α₂ + α₃ - 1 - Q.h)) (μ - ((p - r : ℤ) : ℂ)) k := by
  have hN := prodFunZ_assoc_right_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ h₁ h₂ h₃ hf hu p hNA hN₁ hN₃
  intro μ k
  have hU := isOpen_overlapDomain
  have hs := overlapDomain_subset
  have hne := overlapDomain_nonempty
  set S := α₁ + α₂ + α₃ - h₄ - 2 + β - p - 1 with hSdef
  set ν := α₂ + α₃ - 1 - Q.h with hνdef
  set FA : ℕ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (p - i)) w₁ w₂ w₃
    (S + ((i : ℤ) : ℂ)) (ν + ((i : ℤ) : ℂ)) with hFA
  set FB : ℕ → ℂ → ℂ := fun i => prodFunZ Y₁ Y₂ f w₁ w₂ (mode (P₃.isMod.YM u) i w₃)
    (S + ((p - i : ℤ) : ℂ)) (ν + ((p - i : ℤ) : ℂ)) with hFB
  set FC : ℕ → ℂ → ℂ := fun r => prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r w₁) w₂ w₃
    (S + ((p - r : ℤ) : ℂ)) ν with hFC
  have eA : ∀ i, HasLogExp overlapDomain (FA i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂ h₃
      (supportedAt_comp_mode hf hu (p - i)) (by rw [hSdef]; push_cast; ring) i
      (by rw [hνdef])
  have eB : ∀ i, HasLogExp overlapDomain (FB i) := fun i =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₁ h₂
      (VOA.mode_mem_weight P₃.isMod hu h₃ i) hf (by rw [hSdef]; push_cast; ring) (p + 1 - β)
      (by rw [hνdef]; push_cast; ring)
  have eC : ∀ r, HasLogExp overlapDomain (FC r) := fun r =>
    prodFunZ_hasLogExp_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
      (VOA.mode_mem_weight P₁.isMod hu h₁ r) h₂ h₃ hf (by rw [hSdef]; push_cast; ring) 0
      (by rw [hνdef]; push_cast; ring)
  have eA' : ∀ i : ℕ, HasLogExp overlapDomain (fun t => negOnePow i * cbz p i * FA i t) :=
    fun i => hasLogExp_smul _ (eA i)
  have eB' : ∀ i : ℕ, HasLogExp overlapDomain (fun t => negOnePow i * cbz p i * FB i t) :=
    fun i => hasLogExp_smul _ (eB i)
  have eC' : ∀ r : ℕ, HasLogExp overlapDomain
      (fun t => cbz p r * (Complex.exp (((p - r : ℤ) : ℂ) * t) * FC r t)) :=
    fun r => hasLogExp_smul _ (hasLogExp_exp_mul (eC r) _)
  have eSA := hasLogExp_sum (Finset.range NA) (fun i _ => eA' i)
  have eSB := hasLogExp_smul (negOnePow p) (hasLogExp_sum (Finset.range N₃) (fun i _ => eB' i))
  have eSC := hasLogExp_sum (Finset.range N₁) (fun r _ => eC' r)
  have hsum : ∀ t ∈ overlapDomain,
      prodFunZ Y₁ Y₂ f w₁ (mode (P₂.isMod.YM u) p w₂) w₃ S ν t
        = (((fun t => ∑ i ∈ Finset.range NA, negOnePow i * cbz p i * FA i t)
            + fun t => -(negOnePow p * ∑ i ∈ Finset.range N₃, negOnePow i * cbz p i * FB i t))
          + fun t => -(∑ r ∈ Finset.range N₁,
              cbz p r * (Complex.exp (((p - r : ℤ) : ℂ) * t) * FC r t))) t := by
    intro t ht
    rw [hN t ht]
    simp only [Pi.add_apply, hFA, hFB, hFC]
    rw [sub_eq_add_neg, sub_eq_add_neg]
    congr 2
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have eSB' := hasLogExp_smul (-1) eSB
  have eSC' := hasLogExp_smul (-1) eSC
  simp only [neg_one_mul] at eSB' eSC'
  have eAB := hasLogExp_add eSA eSB'
  rw [logCoeff_congr hU hs hne hsum (hasLogExp_congr (fun t ht => (hsum t ht).symm)
      (hasLogExp_add eAB eSC')),
    logCoeff_add hU hs hne eAB eSC', logCoeff_add hU hs hne eSA eSB']
  have nB : logCoeff overlapDomain
      (fun t => -(negOnePow p * ∑ i ∈ Finset.range N₃, negOnePow i * cbz p i * FB i t)) μ k
      = -(negOnePow p * ∑ i ∈ Finset.range N₃, negOnePow i * cbz p i
          * logCoeff overlapDomain (FB i) μ k) := by
    have := logCoeff_smul hU hs hne (-1) eSB μ k
    simp only [neg_one_mul] at this
    rw [this, logCoeff_smul hU hs hne _ (hasLogExp_sum (Finset.range N₃) (fun i _ => eB' i)),
      logCoeff_sum hU hs hne _ (fun i _ => eB' i)]
    congr 2
    exact Finset.sum_congr rfl fun i _ => logCoeff_smul hU hs hne _ (eB i) μ k
  have nC : logCoeff overlapDomain (fun t => -(∑ r ∈ Finset.range N₁,
      cbz p r * (Complex.exp (((p - r : ℤ) : ℂ) * t) * FC r t))) μ k
      = -(∑ r ∈ Finset.range N₁, cbz p r
          * logCoeff overlapDomain (FC r) (μ - ((p - r : ℤ) : ℂ)) k) := by
    have := logCoeff_smul hU hs hne (-1) eSC μ k
    simp only [neg_one_mul] at this
    rw [this, logCoeff_sum hU hs hne _ (fun r _ => eC' r)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [logCoeff_smul hU hs hne _ (hasLogExp_exp_mul (eC r) _)]
    congr 1
    have := logCoeff_exp_mul hU hs hne (eC r) (((p - r : ℤ) : ℂ)) (μ - ((p - r : ℤ) : ℂ)) k
    rw [sub_add_cancel] at this
    exact this
  rw [nB, nC, logCoeff_sum hU hs hne _ (fun i _ => eA' i)]
  simp only [sub_eq_add_neg]
  congr 2
  exact Finset.sum_congr rfl fun i _ => logCoeff_smul hU hs hne _ (eA i) μ k

end Holds

/-! ## The coproduct on the coefficient functions -/

/-- `prodFunZ` on an integer shift of the canonical base is the canonical `prodFun`. -/
theorem prodFunZ_canonical {P₂ P₃ P₁ P₄ Q : LWModule W}
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (w₁ : P₁.carrier) {α₂ α₃ : ℂ} {w₂ : P₂.carrier} {w₃ : P₃.carrier}
    (h₂ : w₂ ∈ P₂.isMod.weight α₂) (h₃ : w₃ ∈ P₃.isMod.weight α₃) (S : ℂ) (d : ℤ) (ν : ℂ)
    (hν : ν = α₂ + α₃ - 1 - Q.h + d) :
    prodFunZ Y₁ Y₂ f w₁ w₂ w₃ S ν = prodFun Y₁ Y₂ f w₁ w₂ w₃ S (α₂ + α₃ - 1 - Q.h) := by
  funext t
  rw [hν, prodFunZ_shift, prodFunZ_eq_prodFun f w₁ (isBase_canonical Q hY₂ h₂ h₃)]

/-- `(w₁, u_p w₂)` as a homogeneous pair. -/
def pairRight {P₁ P₂ : LWModule W} (x : HomPair P₁ P₂) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (p : ℤ) : HomPair P₁ P₂ :=
  ⟨x.w₁, x.α₁, mode (P₂.isMod.YM u) p x.w₂, x.α₂ + β - p - 1, x.h₁,
    VOA.mode_mem_weight P₂.isMod hu x.h₂ p⟩

/-- `(u_r w₁, w₂)` as a homogeneous pair. -/
def pairLeft {P₁ P₂ : LWModule W} (x : HomPair P₁ P₂) {β : ℤ} {u : 𝒱}
    (hu : u ∈ W.grading β) (r : ℤ) : HomPair P₁ P₂ :=
  ⟨mode (P₁.isMod.YM u) r x.w₁, x.α₁ + β - r - 1, x.w₂, x.α₂,
    VOA.mode_mem_weight P₁.isMod hu x.h₁ r, x.h₂⟩

/-- **The transposed coproduct of `u_p` on a coefficient function is an outside action**:
`B_{n,k}(f,w₃)(w₁, u_p w₂) + Σᵣ C(p,r) B_{n,k}(f,w₃)(u_r w₁, w₂)
  = Σᵢ (−1)ⁱC(p,i) B_{n',k}(f∘u_{p−i}, w₃)(w₁,w₂) − (−1)^p Σᵢ (−1)ⁱC(p,i) B_{n',k}(f, uᵢw₃)(w₁,w₂)`,
`n' = n − β + p + 1`; same log index `k`. -/
theorem coefFun_coproduct_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (p : ℤ) (x : HomPair P₁ P₂) {NA N₁ N₃ : ℕ}
    (hNA : ∀ i : ℕ, NA ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (p - i) = 0)
    (hN₁ : ∀ r : ℕ, N₁ ≤ r → mode (P₁.isMod.YM u) r x.w₁ = 0)
    (hN₃ : ∀ i : ℕ, N₃ ≤ i → mode (P₃.isMod.YM u) i w₃ = 0) :
    ∀ (n : ℂ) (k : ℕ),
    coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairRight x hu p)
        + ∑ r ∈ Finset.range N₁, cbz p r * coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairLeft x hu r)
      = ∑ i ∈ Finset.range NA, negOnePow i * cbz p i
          * coefFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (p - i)) w₃ α₃ (h₄ - β + (p - i : ℤ) + 1)
              (n - β + p + 1) k x
        - negOnePow p * ∑ i ∈ Finset.range N₃, negOnePow i * cbz p i
          * coefFun Y₁ Y₂ f (mode (P₃.isMod.YM u) i w₃) (α₃ + β - i - 1) h₄
              (n - β + p + 1) k x := by
  have hN := logCoeff_assoc_right_holds hV i₁ i₂ i₃ i₄ hY₁ hY₂ x.h₁ x.h₂ h₃ hf
    hu iQ p hNA hN₁ hN₃
  intro n k
  have key := hN (n - x.α₁ - (x.α₂ + β - p - 1)) k
  -- rewrite every `prodFunZ` as the canonical `prodFun`
  rw [prodFunZ_canonical hY₂ f x.w₁ (VOA.mode_mem_weight P₂.isMod hu x.h₂ p) h₃ _ (-(β - p - 1))
    _ (by push_cast; ring)] at key
  have eA : ∀ i : ℕ, prodFunZ Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (p - i)) x.w₁ x.w₂ w₃
      (x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - p - 1 + ((i : ℤ) : ℂ))
      (x.α₂ + α₃ - 1 - Q.h + ((i : ℤ) : ℂ))
      = prodFun Y₁ Y₂ (f ∘ₗ mode (P₄.isMod.YM u) (p - i)) x.w₁ x.w₂ w₃
          (x.α₁ + x.α₂ + α₃ - (h₄ - β + (p - i : ℤ) + 1) - 2) (x.α₂ + α₃ - 1 - Q.h) := by
    intro i
    rw [prodFunZ_canonical hY₂ _ x.w₁ x.h₂ h₃ _ i _ rfl]
    congr 1
    push_cast; ring
  have eB : ∀ i : ℕ, prodFunZ Y₁ Y₂ f x.w₁ x.w₂ (mode (P₃.isMod.YM u) i w₃)
      (x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - p - 1 + ((p - i : ℤ) : ℂ))
      (x.α₂ + α₃ - 1 - Q.h + ((p - i : ℤ) : ℂ))
      = prodFun Y₁ Y₂ f x.w₁ x.w₂ (mode (P₃.isMod.YM u) i w₃)
          (x.α₁ + x.α₂ + (α₃ + β - i - 1) - h₄ - 2) (x.α₂ + (α₃ + β - i - 1) - 1 - Q.h) := by
    intro i
    have hw := VOA.mode_mem_weight P₃.isMod hu h₃ i
    rw [prodFunZ_canonical hY₂ f x.w₁ x.h₂ hw _ (p + 1 - β) _ (by push_cast; ring)]
    congr 1
    push_cast; ring
  have eC : ∀ r : ℕ, prodFunZ Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
      (x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - p - 1 + ((p - r : ℤ) : ℂ))
      (x.α₂ + α₃ - 1 - Q.h)
      = prodFun Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
          ((x.α₁ + β - r - 1) + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h) := by
    intro r
    rw [prodFunZ_canonical hY₂ f _ x.h₂ h₃ _ 0 _ (by push_cast; ring)]
    congr 1
    push_cast; ring
  simp only [eA, eB, eC] at key
  have key2 := congrArg (fun z => z + ∑ r ∈ Finset.range N₁, cbz p r
      * logCoeff overlapDomain (prodFun Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
          ((x.α₁ + β - r - 1) + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h))
          (n - x.α₁ - (x.α₂ + β - p - 1) - ((p - r : ℤ) : ℂ)) k) key
  simp only [sub_add_cancel] at key2
  simp only [coefFun, pairRight, pairLeft, prodExpCoeff]
  rw [show x.α₁ + (x.α₂ + (β : ℂ) - (p : ℂ) - 1) + α₃ - h₄ - 2
      = x.α₁ + x.α₂ + α₃ - h₄ - 2 + β - p - 1 by ring,
    show n - (β : ℂ) + p + 1 - x.α₁ - x.α₂ = n - x.α₁ - (x.α₂ + β - p - 1) by ring]
  have hC : ∑ r ∈ Finset.range N₁, cbz p r
      * logCoeff overlapDomain (prodFun Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
          (x.α₁ + β - ((r : ℤ) : ℂ) - 1 + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h))
          (n - (x.α₁ + β - ((r : ℤ) : ℂ) - 1) - x.α₂) k
      = ∑ r ∈ Finset.range N₁, cbz p r
      * logCoeff overlapDomain (prodFun Y₁ Y₂ f (mode (P₁.isMod.YM u) r x.w₁) x.w₂ w₃
          ((x.α₁ + β - r - 1) + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h))
          (n - x.α₁ - (x.α₂ + β - p - 1) - ((p - r : ℤ) : ℂ)) k :=
    Finset.sum_congr rfl fun r _ => by congr 2; push_cast; ring
  rw [hC]
  exact key2

/-- `B_{n,k}` vanishes when an argument is zero. -/
theorem coefFun_eq_zero_of {P₁ P₂ P₃ P₄ Q : LWModule W}
    (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ)
    (w₃ : P₃.carrier) (α₃ h₄ n : ℂ) (k : ℕ) (x : HomPair P₁ P₂)
    (h : x.w₁ = 0 ∨ x.w₂ = 0 ∨ w₃ = 0 ∨ f = 0) : coefFun Y₁ Y₂ f w₃ α₃ h₄ n k x = 0 := by
  simp only [coefFun, prodExpCoeff]
  rw [prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ h]
  exact logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty _ _

/-- **Lower truncation of the coproduct on the coefficient functions**: for homogeneous
`u` there is `P` such that `Δᵀ(u_p) B_{n,k}(f, w₃) = 0` for all `p ≤ P` (uniformly in the inside
data).  With FHL (5.2.4) this is the lower truncation of the Huang–Lepowsky `P(1)`-action on the
span of the coefficient functionals (`v'_m` is a finite combination of
`(L₁ʲv)^ᵀ_{2 wt v − m − 2 − j}`,
and `m → ∞` means `p → −∞`). -/
theorem coproduct_lower_truncation (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂)
    {α₃ h₄ : ℂ} {w₃ : P₃.carrier} {f : P₄.carrier →ₗ[ℂ] ℂ}
    (h₃ : w₃ ∈ P₃.isMod.weight α₃) (hf : SupportedAt P₄.isMod f h₄)
    {β : ℤ} {u : 𝒱} (hu : u ∈ W.grading β) (n : ℂ) (k : ℕ) :
    ∃ P : ℤ, ∀ p ≤ P, ∀ x : HomPair P₁ P₂, ∃ N₁ : ℕ,
      (∀ r : ℕ, N₁ ≤ r → mode (P₁.isMod.YM u) r x.w₁ = 0) ∧
      coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairRight x hu p)
        + ∑ r ∈ Finset.range N₁, cbz p r * coefFun Y₁ Y₂ f w₃ α₃ h₄ n k (pairLeft x hu r) = 0 := by
  obtain ⟨M, hM⟩ := VOA.Huang.LogRemovalWeightBound.coefFun_eq_zero_of_re_lt hV i₁ i₂ i₃ i₄ iQ
    hY₁ hY₂
  obtain ⟨N₃, hN₃⟩ := exists_nat_truncation P₃.isMod u w₃
  obtain ⟨P₀, hP₀⟩ := exists_int_lt (min ((P₄.h - h₄ + β - 1).re)
    (M - (α₃ + β - 1).re - h₄.re - (n - β + 1).re))
  refine ⟨P₀, fun p hp x => ?_⟩
  obtain ⟨N₁, hN₁⟩ := exists_nat_truncation P₁.isMod u x.w₁
  refine ⟨N₁, hN₁, ?_⟩
  have hpr : (p : ℝ) < min ((P₄.h - h₄ + β - 1).re)
      (M - (α₃ + β - 1).re - h₄.re - (n - β + 1).re) :=
    lt_of_le_of_lt (by exact_mod_cast hp) hP₀
  have hp1 := lt_of_lt_of_le hpr (min_le_left _ _)
  have hp2 := lt_of_lt_of_le hpr (min_le_right _ _)
  have hA : ∀ i : ℕ, 0 ≤ i → f ∘ₗ mode (P₄.isMod.YM u) (p - i) = 0 := by
    intro i _
    refine comp_mode_eq_zero_of_lt P₄.isLow hf hu ?_
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re] at hp1 ⊢
    push_cast
    linarith
  rw [coefFun_coproduct_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ h₃ hf hu p x hA hN₁ hN₃ n k]
  rw [Finset.range_zero, Finset.sum_empty, zero_sub, neg_eq_zero]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ?_)
  have hw : mode (P₃.isMod.YM u) i w₃ ∈ P₃.isMod.weight (α₃ + β - i - 1) := by
    have := VOA.mode_mem_weight P₃.isMod hu h₃ i
    simpa using this
  rw [hM _ _ _ _ hw hf _ k, Pi.zero_apply, mul_zero]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  simp only [Complex.add_re, Complex.sub_re, Complex.intCast_re, Complex.one_re,
    Complex.natCast_re] at hp2 ⊢
  linarith

end VOA.Huang.AssocTauStable
