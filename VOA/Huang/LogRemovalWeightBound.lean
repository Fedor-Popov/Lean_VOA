/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.LogRemovalBound

/-!
# A lower bound on the intermediate weights, per outside datum

For fixed irreducible modules and intertwiners of a strongly rational `V`, the coefficient
functions `B_{n,k}(f, w₃)` of the products at the iterate point vanish identically (in the inside
data `(w₁, w₂)`) as soon as `Re n < M − Re α₃ − Re h₄` (`α₃ = wt w₃`, `h₄` the weight carrying
`f`), for one constant `M` (`coefFun_eq_zero_of_re_lt`).

This is exactly the input needed for the **lower truncation** of the Huang–Lepowsky `P(1)`-action
on the span of the coefficient functionals: the action `τ(v, m)` sends `B_n(f, w₃)` to a finite
combination of `B_{n'}(f', w₃')` with `n' = n + wt v − m − 1 → −∞` and with *finitely many*
outside data `(f', w₃')` (`f' = f ∘ v_q`, `w₃' = v_q w₃`), so `τ(v, m) B = 0` for `m ≫ 0`.
⚠ It is **not** automatic: the residue of the `v`-insertion at the point of `w₃` contributes
for every `m`; only this bound kills it.  The bound is *not* uniform in the outside data (it
degrades with their levels), which is why a uniform lower bound for the whole span `Λ` (needed for
`ℕ`-gradability) is a separate, open step.

**Proof.**  As in `LogRemovalBound`, with "log-degree `≤ K`" replaced by "no exponent of real
part `< M`" (`ExpGE`): this is preserved by sums, by multiplication by convergent power series in
`u` and shifted by multiplication by `u^ν`; the renormalization `(1 − x)^{−s}` shifts it by the
total level `s`, and `s − N₁ − N₂ = N₃ + N₄`.

## Main results
* `ExpGE`, `expModule` (a `ℂ[x]`-module), `expGE_bounded_holds`,
  `coefFun_eq_zero_of_re_lt`.

## Status
No `sorry`, no new axioms.
-/

namespace VOA.Huang.LogRemovalWeightBound

open VOA PowerSeries VOA.Huang.MatrixCoeff VOA.Huang.FusionTop VOA.Huang.AssocTarget
open VOA.Huang.AssocExpansion VOA.Huang.LogRemovalCoeff VOA.Huang.AssocCoeffReduction
open VOA.Huang.AssocCoeffRules VOA.Huang.LogRemovalSemisimple VOA.Huang.LogRemovalAdmissible
open VOA.Huang.HuangODEProduct VOA.Huang.HuangODEIterPoint VOA.Huang.HuangODEAlgebra
open VOA.Huang.LogRemovalBound
open VOA.Huang.FrobeniusLog (psEval)
open scoped BigOperators

universe u

/-! ## Functions with exponents bounded below -/

section Exp

/-- `F` has a log-expansion on the overlap domain with no exponent of real part `< M`. -/
def ExpGE (M : ℝ) (F : ℂ → ℂ) : Prop :=
  HasLogExp overlapDomain F ∧ ∀ μ k, μ.re < M → logCoeff overlapDomain F μ k = 0

theorem ExpGE.mono {M M' : ℝ} {F : ℂ → ℂ} (h : ExpGE M F) (hM : M' ≤ M) : ExpGE M' F :=
  ⟨h.1, fun μ k hk => h.2 μ k (by linarith)⟩

theorem ExpGE.congr {M : ℝ} {F G : ℂ → ℂ} (h : ExpGE M F)
    (hFG : ∀ t ∈ overlapDomain, F t = G t) : ExpGE M G :=
  ⟨hasLogExp_congr hFG h.1, fun μ k hk => by
    rw [← logCoeff_congr isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hFG h.1]
    exact h.2 μ k hk⟩

theorem expGE_zero (M : ℝ) : ExpGE M (fun _ => 0) :=
  ⟨hasLogExp_zero, fun μ k _ =>
    logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty μ k⟩

theorem ExpGE.add {M : ℝ} {F G : ℂ → ℂ} (hF : ExpGE M F) (hG : ExpGE M G) :
    ExpGE M (F + G) :=
  ⟨hasLogExp_add hF.1 hG.1, fun μ k hk => by
    rw [logCoeff_add isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hF.1 hG.1,
      hF.2 μ k hk, hG.2 μ k hk, add_zero]⟩

theorem ExpGE.psEval_mul {M : ℝ} {F : ℂ → ℂ} (hF : ExpGE M F) {c : PowerSeries ℂ}
    (hc : c ∈ SubexpPS) : ExpGE M (fun t => psEval c (Complex.exp t) * F t) :=
  ⟨hasLogExp_psEval_mul overlapDomain_subset hF.1 hc, fun μ k hk => by
    rw [logCoeff_psEval_mul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      hF.1 hc]
    have : ∀ m : ℕ, PowerSeries.coeff m c * logCoeff overlapDomain F (μ - m) k = 0 := by
      intro m
      rw [hF.2 _ k (by simp only [Complex.sub_re, Complex.natCast_re]; linarith
        [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]), mul_zero]
    simp [this]⟩

theorem ExpGE.exp_mul {M : ℝ} {F : ℂ → ℂ} (hF : ExpGE M F) (ν : ℂ) :
    ExpGE (M + ν.re) (fun t => Complex.exp (ν * t) * F t) :=
  ⟨hasLogExp_exp_mul hF.1 ν, fun μ k hk => by
    have := logCoeff_exp_mul isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty
      hF.1 ν (μ - ν) k
    rw [sub_add_cancel] at this
    rw [this, hF.2 _ k (by simp only [Complex.sub_re]; linarith)]⟩

/-- Every function with a log-expansion has exponents bounded below. -/
theorem exists_expGE {F : ℂ → ℂ} (hF : HasLogExp overlapDomain F) : ∃ M : ℝ, ExpGE M F := by
  classical
  obtain ⟨E, hE⟩ := hF
  refine ⟨-∑ j, |(E.lam j).re|, ⟨E, hE⟩, fun μ k hμ => ?_⟩
  rw [logCoeff_eq isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty hE]
  refine Finset.sum_eq_zero fun j _ => exCoeff_of_forall_ne (fun n hn => ?_) _ _
  have h1 : μ.re = (E.lam j).re + n := by rw [← hn]; simp
  have h2 : -|(E.lam j).re| ≤ (E.lam j).re := neg_abs_le _
  have h3 : |(E.lam j).re| ≤ ∑ j, |(E.lam j).re| :=
    Finset.single_le_sum (f := fun j => |(E.lam j).re|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
  have h4 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end Exp

/-- **Series whose values have exponents `≥ M` form a `ℂ[x]`-module.** -/
noncomputable def expModule (c₀ : ℂ) (M : ℝ) : Submodule (ratRing 0) (PowerSeries ℂ) where
  carrier := {Z | Z ∈ SubexpPS ∧ ExpGE M (Phi c₀ Z)}
  zero_mem' := ⟨SubexpPS.zero_mem, (expGE_zero M).congr fun t _ => by
    simp [Phi, psEval_zero']⟩
  add_mem' := by
    rintro A B ⟨hA, hA'⟩ ⟨hB, hB'⟩
    refine ⟨SubexpPS.add_mem hA hB, (hA'.add hB').congr fun t ht => ?_⟩
    simp only [Phi, Pi.add_apply]
    rw [psEval_add hA hB (norm_xt_lt_one ht)]
    ring
  smul_mem' := by
    rintro ⟨r, hr⟩ Z ⟨hZ, hZ'⟩
    have hrs := subexp_of_mem_ratRing_zero hr
    obtain ⟨c, hc, hcr⟩ := exists_subexp_of_mem_ratRing_zero hr
    refine ⟨?_, (hZ'.psEval_mul hc).congr fun t ht => ?_⟩
    · rw [Subalgebra.smul_def]
      exact SubexpPS.mul_mem hrs hZ
    · simp only [Phi]
      rw [show (⟨r, hr⟩ : ratRing 0) • Z = r * Z from rfl,
        psEval_mul hrs hZ (norm_xt_lt_one ht), hcr _ (norm_exp_lt_one ht)]
      simp only [xt]
      ring

section Main

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-- **Exponents of products at the iterate point are bounded below by `M − s`**, `s` the
total level of the four vectors (strongly rational `V`, irreducible modules). -/
theorem expGE_bounded_holds (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂) :
    ∃ M : ℝ, ∀ (N₁ N₂ N₃ N₄ : ℕ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier)
      (f : P₄.carrier →ₗ[ℂ] ℂ), w₁ ∈ P₁.isMod.weight (P₁.h + N₁) →
      w₂ ∈ P₂.isMod.weight (P₂.h + N₂) → w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
      SupportedAt P₄.isMod f (P₄.h + N₄) →
      ExpGE (M - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℝ)) (prodFun Y₁ Y₂ f w₁ w₂ w₃
        ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
        ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h)) := by
  classical
  have h2 := VOA.Huang.BuhlSpanning.moduleC2Input_holds.{u}
  have hC : ModuleC1Data W := VOA.Huang.HuangODEC1.moduleC1Data_of_C2
    (fun P hP => h2 𝒱 W hV P hP)
    (VOA.Huang.HuangODEDual.moduleDualC1Data_of_contragredientC2
      (VOA.Huang.HuangODEContra.contragredientC2Data_of_moduleC2Input h2 hV))
  obtain ⟨B₁, c₁⟩ := (hC P₁ i₁).1
  obtain ⟨B₂, c₂⟩ := (hC P₂ i₂).1
  obtain ⟨B₃, c₃⟩ := (hC P₃ i₃).1
  obtain ⟨B₄, d₄⟩ := (hC P₄ i₄).2
  set c₀ : ℂ := P₁.h - P₄.h - 1 + Q.h with hc₀
  set ν₀ : ℂ := P₂.h + P₃.h - 1 - Q.h with hν₀
  obtain ⟨K₀, hUB⟩ := exists_unifBase (A₅ := Q.isMod) hY₂ P₂.h P₃.h ν₀ 0
  set ν : ℂ := ν₀ - ((0 : ℕ) : ℂ) + K₀ with hν
  set cc : ℂ := P₁.h + P₂.h + P₃.h - P₄.h - 2 with hcc
  have hZ : ∀ (N₁ N₂ N₃ N₄ : ℕ) (f : P₄.carrier →ₗ[ℂ] ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier)
      (w₃ : P₃.carrier), w₁ ∈ P₁.isMod.weight (P₁.h + N₁) →
      w₂ ∈ P₂.isMod.weight (P₂.h + N₂) → w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
      (1 - X) ^ (N₁ + N₂ + N₃ + N₄) * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
        = (1 - X) ^ (N₁ + N₂ + N₃ + N₄) * (X ^ (K₀ + N₁ + N₄) * prodSeries Y₁ Y₂ f w₁ w₂ w₃
            ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
            ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h)) := by
    intro N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃
    have hb := isBase_canonical Q hY₂ hw₂ hw₃
    have e : ν = ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h) - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ)
        + ((K₀ + N₁ + N₄ : ℕ) : ℂ) := by
      rw [hν, hν₀]; push_cast; ring
    rw [e, QT_eq_X_pow_mul_prodSeries hb]
  have hσeq : ∀ N₁ N₂ N₃ N₄ : ℕ,
      ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
        - ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h) = c₀ + N₁ - N₄ := by
    intros; rw [hc₀]; ring
  have hgood : ∀ (N₁ N₂ N₃ N₄ : ℕ) (f : P₄.carrier →ₗ[ℂ] ℂ) (w₁ : P₁.carrier)
      (w₂ : P₂.carrier) (w₃ : P₃.carrier), w₁ ∈ P₁.isMod.weight (P₁.h + N₁) →
      w₂ ∈ P₂.isMod.weight (P₂.h + N₂) → w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
      SupportedAt P₄.isMod f (P₄.h + N₄) →
      (1 - X) ^ (N₁ + N₂ + N₃ + N₄) * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ SubexpPS ∧
      (∀ M, ExpGE M (prodFun Y₁ Y₂ f w₁ w₂ w₃
          ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
          ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h)) →
        ExpGE (M + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℝ)) (Phi c₀ ((1 - X) ^ (N₁ + N₂ + N₃ + N₄)
          * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)))) ∧
      (∀ M, ExpGE M (Phi c₀ ((1 - X) ^ (N₁ + N₂ + N₃ + N₄)
          * QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄))) →
        ExpGE (M - ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℝ)) (prodFun Y₁ Y₂ f w₁ w₂ w₃
          ((P₁.h + N₁) + (P₂.h + N₂) + (P₃.h + N₃) - (P₄.h + N₄) - 2)
          ((P₂.h + N₂) + (P₃.h + N₃) - 1 - Q.h))) := by
    intro N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf
    have hG := prodSeries_mem_subexpPS hV i₁ i₂ i₃ i₄ hY₁ hY₂ hw₁ hw₂ hw₃ hf
    rw [hZ N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃]
    refine ⟨SubexpPS.mul_mem (SubexpPS.pow_mem one_sub_X_mem_subexp _)
      (SubexpPS.mul_mem (SubexpPS.pow_mem X_mem_subexp _) hG), fun M hM => ?_, fun M hM => ?_⟩
    · have := ((hM.psEval_mul (binPS_mem
        (-((N₄ : ℤ) - N₁ + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℤ) + ((K₀ + N₁ + N₄ : ℕ) : ℤ))))).exp_mul
        (((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ)))
      simp only [Complex.natCast_re] at this
      exact this.congr fun t ht =>
        (Phi_eq Y₁ Y₂ f w₁ w₂ w₃ _ _ c₀ N₁ N₄ (N₁ + N₂ + N₃ + N₄) (K₀ + N₁ + N₄)
          (hσeq N₁ N₂ N₃ N₄) hG ht).symm
    · have := ((hM.psEval_mul (binPS_mem
        ((N₄ : ℤ) - N₁ + ((N₁ + N₂ + N₃ + N₄ : ℕ) : ℤ) + ((K₀ + N₁ + N₄ : ℕ) : ℤ)))).exp_mul
        (-(((N₁ + N₂ + N₃ + N₄ : ℕ) : ℂ))))
      simp only [Complex.neg_re, Complex.natCast_re, ← sub_eq_add_neg] at this
      exact this.congr fun t ht =>
        (prodFun_eq_Phi Y₁ Y₂ f w₁ w₂ w₃ _ _ c₀ N₁ N₄ (N₁ + N₂ + N₃ + N₄) (K₀ + N₁ + N₄)
          (hσeq N₁ N₂ N₃ N₄) hG ht).symm
  choose T hTfin hTform hTspan using fun q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1)
      × Fin (B₄ + 1) =>
    exists_finite_span_supported (h₁ := P₁.h) (h₂ := P₂.h) (h₃ := P₃.h) (h₄ := P₄.h)
      (ν := ν) hY₁ hY₂ q.1 q.2.1 q.2.2.1 q.2.2.2
  set lev : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) → ℕ :=
    fun q => (q.1 : ℕ) + (q.2.1 : ℕ) + (q.2.2.1 : ℕ) + (q.2.2.2 : ℕ) with hlev
  set S : Set (PowerSeries ℂ) := ⋃ q, (fun g => (1 - X) ^ lev q * g) '' T q with hS
  have hSfin : S.Finite := Set.finite_iUnion fun q => (hTfin q).image _
  have hSgood : ∀ Z ∈ S, ∃ M : ℝ, Z ∈ expModule c₀ M := by
    intro Z hZS
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hZS
    obtain ⟨g, hg, rfl⟩ := hq
    obtain ⟨f, w₁, w₂, w₃, hw₁, hw₂, hw₃, hf, rfl⟩ := hTform q g hg
    obtain ⟨M, hM⟩ := exists_expGE (prod_hasLogExp hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂ hw₁ hw₂ hw₃ hf)
    have hg' := hgood q.1 q.2.1 q.2.2.1 q.2.2.2 f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf
    exact ⟨_, hg'.1, hg'.2.1 M hM⟩
  choose! MZ hMZ using hSgood
  set M : ℝ := -∑ Z ∈ hSfin.toFinset, |MZ Z| with hM
  have hSM : ∀ Z ∈ S, Z ∈ expModule c₀ M := by
    intro Z hZS
    obtain ⟨h1, h2⟩ := hMZ Z hZS
    refine ⟨h1, h2.mono ?_⟩
    have h3 : |MZ Z| ≤ ∑ Z ∈ hSfin.toFinset, |MZ Z| :=
      Finset.single_le_sum (f := fun Z => |MZ Z|) (fun _ _ => abs_nonneg _)
        (hSfin.mem_toFinset.mpr hZS)
    have h4 : -|MZ Z| ≤ MZ Z := neg_abs_le _
    rw [hM]; linarith
  have hbase : ∀ (N₁ N₂ N₃ N₄ : ℕ), N₁ ≤ B₁ → N₂ ≤ B₂ → N₃ ≤ B₃ → N₄ ≤ B₄ →
      ∀ (f : P₄.carrier →ₗ[ℂ] ℂ) (w₁ : P₁.carrier) (w₂ : P₂.carrier) (w₃ : P₃.carrier),
        w₁ ∈ P₁.isMod.weight (P₁.h + N₁) → w₂ ∈ P₂.isMod.weight (P₂.h + N₂) →
        w₃ ∈ P₃.isMod.weight (P₃.h + N₃) →
        (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
          QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄) ∈ expModule c₀ M := by
    intro N₁ N₂ N₃ N₄ b₁ b₂ b₃ b₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃
    set q : Fin (B₁ + 1) × Fin (B₂ + 1) × Fin (B₃ + 1) × Fin (B₄ + 1) :=
      (⟨N₁, by omega⟩, ⟨N₂, by omega⟩, ⟨N₃, by omega⟩, ⟨N₄, by omega⟩) with hq
    have hmem := hTspan q f w₁ w₂ w₃ hw₁ hw₂ hw₃
    have hmem' : (1 - X) ^ (N₁ + N₂ + N₃ + N₄) *
        QT Y₁ Y₂ cc ν f w₁ w₂ w₃ N₄ (N₁ + N₂ + N₃ + N₄)
          ∈ Submodule.span ℂ ((fun g => (1 - X) ^ lev q * g) '' T q) := by
      have := Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℂ ((1 - X) ^ lev q)) hmem
      rw [Submodule.map_span] at this
      exact this
    have hle : Submodule.span ℂ ((fun g => (1 - X) ^ lev q * g) '' T q)
        ≤ (expModule c₀ M).restrictScalars ℂ := by
      rw [Submodule.span_le]
      intro Z hZ'
      exact hSM Z (Set.mem_iUnion.mpr ⟨q, hZ'⟩)
    exact hle hmem'
  have hall := pt_mem hY₁ hY₂ P₁.isLow P₂.isLow P₃.isLow P₄.isLow hUB c₁ c₂ c₃ d₄
    (expModule c₀ M) hbase
  refine ⟨M, fun N₁ N₂ N₃ N₄ w₁ w₂ w₃ f hw₁ hw₂ hw₃ hf => ?_⟩
  have hm := hall _ N₁ N₂ N₃ N₄ rfl f w₁ w₂ w₃ hw₁ hw₂ hw₃
  exact (hgood N₁ N₂ N₃ N₄ f w₁ w₂ w₃ hw₁ hw₂ hw₃ hf).2.2 M hm.2

/-- **Lower bound on the intermediate weights, per outside datum**: for fixed irreducible
modules and intertwiners (strongly rational `V`) there is `M` such that the coefficient function
`B_{n,k}(f, w₃)` vanishes identically whenever `Re n < M − Re α₃ − Re h₄`. -/
theorem coefFun_eq_zero_of_re_lt (hV : StronglyRational W)
    {P₁ P₂ P₃ P₄ Q : LWModule W} (i₁ : P₁.IsIrreducibleLW) (i₂ : P₂.IsIrreducibleLW)
    (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW) (iQ : Q.IsIrreducibleLW)
    {Y₁ : IntertwiningModes P₁.carrier Q.carrier P₄.carrier}
    {Y₂ : IntertwiningModes P₂.carrier P₃.carrier Q.carrier}
    (hY₁ : IsIntertwiningOperator P₁.isMod Q.isMod P₄.isMod Y₁)
    (hY₂ : IsIntertwiningOperator P₂.isMod P₃.isMod Q.isMod Y₂) :
    ∃ M : ℝ, ∀ (α₃ h₄ : ℂ) (w₃ : P₃.carrier) (f : P₄.carrier →ₗ[ℂ] ℂ),
      w₃ ∈ P₃.isMod.weight α₃ → SupportedAt P₄.isMod f h₄ →
      ∀ (n : ℂ) (k : ℕ), n.re < M - α₃.re - h₄.re → coefFun Y₁ Y₂ f w₃ α₃ h₄ n k = 0 := by
  obtain ⟨M₀, hM₀⟩ := expGE_bounded_holds hV i₁ i₂ i₃ i₄ iQ hY₁ hY₂
  refine ⟨M₀ + (P₁.h + P₂.h + P₃.h + P₄.h).re,
    fun α₃ h₄ w₃ f h₃ hf n k hn => ?_⟩
  funext x
  simp only [coefFun, Pi.zero_apply, prodExpCoeff]
  have hzero : prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃ (x.α₁ + x.α₂ + α₃ - h₄ - 2)
      (x.α₂ + α₃ - 1 - Q.h) = (fun _ => 0) → logCoeff overlapDomain (prodFun Y₁ Y₂ f x.w₁ x.w₂ w₃
        (x.α₁ + x.α₂ + α₃ - h₄ - 2) (x.α₂ + α₃ - 1 - Q.h)) (n - x.α₁ - x.α₂) k = 0 := by
    intro h; rw [h]
    exact logCoeff_zero isOpen_overlapDomain overlapDomain_subset overlapDomain_nonempty _ _
  by_cases z₁ : P₁.isMod.weight x.α₁ = ⊥
  · have h0 : x.w₁ = 0 := by have := x.h₁; rw [z₁] at this; exact (Submodule.mem_bot ℂ).mp this
    exact hzero (prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ (Or.inl h0))
  by_cases z₂ : P₂.isMod.weight x.α₂ = ⊥
  · have h0 : x.w₂ = 0 := by have := x.h₂; rw [z₂] at this; exact (Submodule.mem_bot ℂ).mp this
    exact hzero (prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ (Or.inr (Or.inl h0)))
  by_cases z₃ : P₃.isMod.weight α₃ = ⊥
  · have h0 : w₃ = 0 := by rw [z₃] at h₃; exact (Submodule.mem_bot ℂ).mp h₃
    exact hzero (prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _ (Or.inr (Or.inr (Or.inl h0))))
  by_cases z₄ : P₄.isMod.weight h₄ = ⊥
  · exact hzero (prodFun_eq_zero_of_w₁ _ _ _ _ _ _ _ _
      (Or.inr (Or.inr (Or.inr (eq_zero_of_supportedAt_bot hf z₄)))))
  obtain ⟨N₁, e₁⟩ := P₁.isLow x.α₁ z₁
  obtain ⟨N₂, e₂⟩ := P₂.isLow x.α₂ z₂
  obtain ⟨N₃, rfl⟩ := P₃.isLow α₃ z₃
  obtain ⟨N₄, rfl⟩ := P₄.isLow h₄ z₄
  have hw₁ : x.w₁ ∈ P₁.isMod.weight (P₁.h + N₁) := e₁ ▸ x.h₁
  have hw₂ : x.w₂ ∈ P₂.isMod.weight (P₂.h + N₂) := e₂ ▸ x.h₂
  have H := hM₀ N₁ N₂ N₃ N₄ x.w₁ x.w₂ w₃ f hw₁ hw₂ h₃ hf
  rw [e₁, e₂]
  refine H.2 _ k ?_
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re] at hn ⊢
  push_cast
  linarith

end Main

end VOA.Huang.LogRemovalWeightBound
