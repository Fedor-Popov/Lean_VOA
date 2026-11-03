/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.BraidingTranslate

/-!
# Commutativity of intertwining operators

Products of intertwiners in the two orders converge on the **disjoint** regions `|z₁| > |z₂|`
and `|z₂| > |z₁|`, so commutativity is a statement about analytic continuation.  Normalise
`z₁ = 1`, `z₂ = t`.  For irreducible modules of a strongly rational `V`:

* the product `⟨f, 𝒴₁(w₁, 1)𝒴₂(w₂, t)w₃⟩` (`|t| < 1`) equals, for real `2/3 < t < 1`, a finite sum
  of iterates `G_j(t) = ⟨f, 𝒴₃ʲ(𝒴̃ʲ(w₂, t − 1)w₁, 1)w₃⟩` with `𝒴̃ʲ` of type `(Qⱼ / P₂ P₁)` and the
  principal power of the negative real `t − 1` (= the `e^{πi}` branch, the limit from the upper
  half plane) — `CommutativityHalfReal`;
* each `G_j` is an absolutely convergent series in `(t−1)^{s}` on the whole punctured disc
  `0 < |t − 1| < 1` (`AssocTarget.summable_iterValue`), i.e. holomorphic on the upper half disc
  and continuous up to `(0, 1) ∪ (1, 2)`; on real `1 < t < 2` it equals a finite sum of products
  in the **opposite order** `⟨f, 𝒴₅(w₂, t)𝒴₆(w₁, 1)w₃⟩` — `CommutativityInputReal`.

So the product continued through the upper half plane from `|t| < 1` to `|t| > 1` is a finite sum
of reversed products: Huang's commutativity (Huang 2005, CCM 7, §3; Huang 2008, CCM 10, §1), with
the branch fixed by `e^{πi}`.  Both sides of every identity below are honest absolutely
convergent sums (no `tsum` junk).

## Main results
* `commutativityHalfReal_of_assoc : StronglyRational W → AssociativityInput W →
  CommutativityHalfReal W` (associativity + skew-symmetry `BraidingSkew` + translation
  `BraidingTranslate`);
* `commutativityInputReal_of_assoc : StronglyRational W → AssociativityInput W →
  AssociativityConverse W → CommutativityInputReal W`.

## Status
No `sorry`, no new axioms.  `AssociativityInput` is proved modulo library citations
(`PzTensorDecomp.associativityInput_of_DLM`; see `CommutativityDLM.lean`);
`AssociativityConverse` is open (V4).
-/

namespace VOA.Huang.CommutativityTarget

open VOA VOA.SkewIntertwiner VOA.Huang.MatrixCoeff VOA.Huang.AssocTarget
open VOA.Huang.BraidingSkew
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **Half commutativity, real form** (TRUE for strongly rational `W`: Huang 2005 CCM 7 §3).  Every
product of intertwiners among irreducible modules equals, for real `2/3 < t < 1`, a finite sum of
iterates with the **reversed inner pair** `𝒴̃ʲ(w₂, t − 1)w₁` (principal power of `t − 1 < 0`), the
same finite family serving all data.  The right side converges for all `0 < |t − 1| < 1`. -/
def CommutativityHalfReal (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Yt : ∀ j, IntertwiningModes P₂.carrier P₁.carrier (Qs j).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₂.isMod P₁.isMod (Qs j).isMod (Yt j)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    ∀ t : ℝ, 2 / 3 < t → t < 1 →
      prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) 1 t
        = ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) ((t : ℂ) - 1) 1

/-- **Commutativity, real form** (TRUE for strongly rational `W`: Huang 2005 CCM 7 §3, Huang
2008 CCM 10).  For every product `𝒴₁(w₁,1)𝒴₂(w₂,t)` there are finitely many iterates
`G_j(t) = ⟨f, 𝒴₃ʲ(𝒴̃ʲ(w₂, t−1)w₁, 1)w₃⟩` (one analytic function of `t` on the upper half disc
around `1`, continuous to the real axis) and finitely many products in the **opposite order**
`𝒴₅ᵐ(w₂, t)𝒴₆ᵐ(w₁, 1)` with: product `= Σ_j G_j` on `2/3 < t < 1`, and `Σ_j G_j =` Σ reversed
products on `1 < t < 2`. -/
def CommutativityInputReal (W : VertexOperatorAlgebra 𝒱) : Prop :=
  ∀ (P₁ P₂ P₃ P₄ Q : LWModule W), P₁.IsIrreducibleLW → P₂.IsIrreducibleLW →
    P₃.IsIrreducibleLW → P₄.IsIrreducibleLW → Q.IsIrreducibleLW →
  ∀ (Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier)
    (Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier),
    IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁ →
    IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂ →
  ∃ (r : ℕ) (Qs : Fin r → LWModule W) (_ : ∀ j, (Qs j).IsIrreducibleLW)
    (Y₃ : ∀ j, IntertwiningModes (Qs j).carrier P₃.carrier P₄.carrier)
    (Yt : ∀ j, IntertwiningModes P₂.carrier P₁.carrier (Qs j).carrier)
    (s : ℕ) (Rs : Fin s → LWModule W) (_ : ∀ m, (Rs m).IsIrreducibleLW)
    (Y₅ : ∀ m, IntertwiningModes P₂.carrier (Rs m).carrier P₄.carrier)
    (Y₆ : ∀ m, IntertwiningModes P₁.carrier P₃.carrier (Rs m).carrier),
    (∀ j, IsIntertwiningOperator (Qs j).isMod P₃.isMod P₄.isMod (Y₃ j)) ∧
    (∀ j, IsIntertwiningOperator P₂.isMod P₁.isMod (Qs j).isMod (Yt j)) ∧
    (∀ m, IsIntertwiningOperator P₂.isMod (Rs m).isMod P₄.isMod (Y₅ m)) ∧
    (∀ m, IsIntertwiningOperator P₁.isMod P₃.isMod (Rs m).isMod (Y₆ m)) ∧
    ∀ (α₁ α₂ α₃ h₄ : ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₁ ∈ P₁.isMod.weight α₁ → w₂ ∈ P₂.isMod.weight α₂ → w₃ ∈ P₃.isMod.weight α₃ →
      SupportedAt P₄.isMod f h₄ →
    (∀ t : ℝ, 2 / 3 < t → t < 1 →
      prodValue Y₁ Y₂ f w₁ w₂ w₃ (α₁ + α₂ + α₃ - h₄ - 2) (α₂ + α₃ - 1 - Q.h) 1 t
        = ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) ((t : ℂ) - 1) 1) ∧
    (∀ t : ℝ, 1 < t → t < 2 →
      ∑ j, iterValue (Y₃ j) (Yt j) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₂ - 1 - (Qs j).h) ((t : ℂ) - 1) 1
        = ∑ m, prodValue (Y₅ m) (Y₆ m) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
            (α₁ + α₃ - 1 - (Rs m).h) t 1)

variable {W : VertexOperatorAlgebra 𝒱}

/-- The inverse FHL phase `n ↦ e^{πi(n+1)}` (so that `Ω₀ ∘ Ω_{1/ω} = id`). -/
theorem invPhase_succ (n : ℂ) :
    (fun n => (omegaPhase n)⁻¹) (n + 1) = -(fun n => (omegaPhase n)⁻¹) n := by
  simp only [omegaPhase_succ, inv_neg]

theorem invPhase_ne_zero (n : ℂ) : (fun n => (omegaPhase n)⁻¹) n ≠ 0 :=
  inv_ne_zero (omegaPhase_ne_zero n)

/-- **Half commutativity from associativity** (strongly rational `W`). -/
theorem commutativityHalfReal_of_assoc (hV : StronglyRational W) (hA : AssociativityInput W) :
    CommutativityHalfReal W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Y₄, hY₃, hY₄, hassoc⟩ := hA P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  refine ⟨r, Qs, iQs, Y₃,
    fun j => skewModes (Lm1 (Qs j).isMod.toWeakModule) (fun n => (omegaPhase n)⁻¹) (Y₄ j),
    hY₃, fun j => isIntertwiningOperator_skewModes (hY₄ j) invPhase_succ invPhase_ne_zero, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf t ht1 ht2
  have h := hassoc α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf 1 t (by linarith) (by linarith)
  rw [Complex.ofReal_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs := iterValue_eq_skew hV i₁ i₂ i₃ i₄ (hY₃ j) (hY₄ j) h₁ h₂ h₃ hf
    (x := 1 - t) (y := t) (by linarith) (by linarith)
  rw [hs]
  congr 1
  · push_cast; ring
  · push_cast; ring

/-- **Commutativity from associativity and its converse** (strongly rational `W`). -/
theorem commutativityInputReal_of_assoc (hV : StronglyRational W) (hA : AssociativityInput W)
    (hC : AssociativityConverse W) : CommutativityInputReal W := by
  intro P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  obtain ⟨r, Qs, iQs, Y₃, Yt, hY₃, hYt, hhalf⟩ :=
    commutativityHalfReal_of_assoc hV hA P₁ P₂ P₃ P₄ Q i₁ i₂ i₃ i₄ iQ Y₁ Y₂ hY₁ hY₂
  -- the converse, applied to each iterate `(𝒴₃ʲ, 𝒴̃ʲ)` with `P₁ ↔ P₂`
  have hconv := fun j => hC P₂ P₁ P₃ P₄ (Qs j) i₂ i₁ i₃ i₄ (iQs j) (Y₃ j) (Yt j) (hY₃ j) (hYt j)
  choose s Rs iRs Y₅ Y₆ hY₅ hY₆ hprod using hconv
  -- flatten the double family
  set N := ∑ j, s j
  set e := (finSigmaFinEquiv (n := s)).symm
  refine ⟨r, Qs, iQs, Y₃, Yt, N, fun m => Rs (e m).1 (e m).2, fun m => iRs _ _,
    fun m => Y₅ (e m).1 (e m).2, fun m => Y₆ (e m).1 (e m).2, hY₃, hYt,
    fun m => hY₅ _ _, fun m => hY₆ _ _, ?_⟩
  intro α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf
  refine ⟨hhalf α₁ α₂ α₃ h₄ w₁ w₂ w₃ f h₁ h₂ h₃ hf, fun t ht1 ht2 => ?_⟩
  have hsum : ∀ g : (Σ j : Fin r, Fin (s j)) → ℂ, ∑ m : Fin N, g (e m) = ∑ j, ∑ k, g ⟨j, k⟩ := by
    intro g
    rw [show (∑ m : Fin N, g (e m)) = ∑ q : (Σ j : Fin r, Fin (s j)), g q from
      Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_sigma]
  rw [hsum (fun q => prodValue (Y₅ q.1 q.2) (Y₆ q.1 q.2) f w₂ w₁ w₃ (α₁ + α₂ + α₃ - h₄ - 2)
    (α₁ + α₃ - 1 - (Rs q.1 q.2).h) (t : ℂ) 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := hprod j α₂ α₁ α₃ h₄ w₂ w₁ w₃ f h₂ h₁ h₃ hf t 1 (by linarith) (by linarith)
  rw [show α₂ + α₁ + α₃ - h₄ - 2 = α₁ + α₂ + α₃ - h₄ - 2 by ring,
    show α₂ + α₁ - 1 - (Qs j).h = α₁ + α₂ - 1 - (Qs j).h by ring, Complex.ofReal_one] at h
  rw [show ((t : ℂ) - 1) = ((t - 1 : ℝ) : ℂ) by push_cast; ring, h]

end VOA.Huang.CommutativityTarget
