/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SquareBracketC2
import VOA.Modularity.ZhuBlockConditions

/-!
# Zhu's finiteness: a genus-one block is determined by finitely many values

The first half of Zhu's Theorem 5.3.2 is that the space of genus-one conformal blocks is
**finite-dimensional**.  Its algebraic core — the part that does not need any analysis — is:

  a linear `S : 𝒱 → ℂ⟦q⟧` obeying Zhu's block condition (ii) is **determined by its values
  on the finite generating family** of `Modularity.C2Extraction` / `Modularity.SquareBracketC2`.

That is proved here, unconditionally.

## The mechanism

Condition (ii) (`IsFormalBlock.negTwo`, i.e. `zhuRecursion_neg_two`) reads

  `S(a[−2]v) = − Σ_{k ≥ 1} (2k−1)·G_{2k} ⋆ S(a[2k−2]v)`,

and the modes on the right are `2k−2 ≥ 0`, so — by the triangularity `a[m]v = Σ_{i ≥ m} c·a₍ᵢ₎v`
of `Modularity.SquareBracketC2` — every `a[2k−2]v` is a combination of vectors of degree
`≤ wt a + wt v − 1`, strictly below the degree `wt a + wt v + 1` of `a₍₋₂₎v`.  Meanwhile
`a₍₋₂₎v = a[−2]v − sqDefect` with the defect also strictly lower.  So a strong induction on the
degree, run inside the **kernel** `ker D` (a submodule, which is what makes the `finsum`
bookkeeping painless), kills everything not already in the generating family.

## Contents

* `NegTwoLaw` — the linearised block condition (ii).
* `vSqZ_mem_of_lower` — triangularity as a membership statement.
* **`eq_zero_of_negTwoLaw_of_vanish`** — the determinacy.
* `eq_of_negTwoLaw_of_eqOn` — two blocks agreeing on the generators agree everywhere
  (with the difference's law as an explicit hypothesis, since `qConv` is only additive where the
  defining sums converge — `qConv_add_apply`).
* `blockDeterminedBy_of_C2Cofinite` — the packaged statement for a `C₂`-cofinite VOA: the
  determining family is finite.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.  Residual toward Zhu Thm 5.3.2: the *analytic* half
— that the finitely many determining functions span a finite-dimensional space of solutions of a
modular linear differential equation (needs holomorphy on `ℍ` and the analytic `G_{2k}`).
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Determinacy

variable {W : VertexOperatorAlgebra 𝒱}

/-- **The linearised block condition (ii).**  `IsFormalBlock.negTwo` is exactly this. -/
def NegTwoLaw (W : VertexOperatorAlgebra 𝒱) (D : 𝒱 →ₗ[ℂ] FormalQSeries) : Prop :=
  ∀ (ka : ℕ), 1 ≤ ka → ∀ a ∈ W.grading (ka : ℤ), ∀ v : 𝒱,
    D (vSqZ W a ka (-2) v)
      + ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
          • qConv (zhuG (m + 1)) (D (vSqZ W a ka (2 * (m + 1) - 2 : ℤ) v)) = 0

theorem IsFormalBlock.negTwoLaw {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hS : IsFormalBlock W S) :
    NegTwoLaw W S := hS.negTwo

/-- **Triangularity as a membership statement**: `a[m]v` lies in any submodule containing all
graded pieces of degree `≤ wt a + wt v − m − 1`. -/
theorem vSqZ_mem_of_lower (W : VertexOperatorAlgebra 𝒱) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (p' : ℕ) (m : ℤ) (T : Submodule ℂ 𝒱)
    (hT : ∀ d : ℤ, d ≤ p + q - m - 1 → W.grading d ≤ T) :
    vSqZ W a p' m b ∈ T := by
  rw [vSqZ_apply]
  refine finsum_mem_submodule_pd _ _ (fun i => ?_)
  rcases lt_or_ge i m with hlt | hge
  · rw [sqBracketCoeffZ_of_lt _ hlt, zero_smul]; exact Submodule.zero_mem _
  · refine Submodule.smul_mem _ _ ?_
    have hmem : W.smul a i b ∈ W.grading (p + q - i - 1) := W.smul_mem_grading ha hb i
    exact hT _ (by omega) hmem

/-- **Zhu's determinacy.**  A linear `D : 𝒱 → ℂ⟦q⟧` satisfying block condition (ii) and
vanishing on a homogeneous family `S` that spans `𝒱` modulo `C₂(𝒱)` vanishes identically. -/
theorem eq_zero_of_negTwoLaw_of_vanish (D : 𝒱 →ₗ[ℂ] FormalQSeries) (hD : NegTwoLaw W D)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hvan : ∀ x ∈ S, D x = 0) : D = 0 := by
  classical
  set K : Submodule ℂ 𝒱 := LinearMap.ker D with hK
  have hSK : Submodule.span ℂ S ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    exact hvan x hx
  -- every graded piece lies in the kernel
  have hgrad : ∀ n : ℤ, W.grading n ≤ K := by
    intro n
    rcases lt_or_ge n 0 with hneg | hnn
    · rw [W.positivity n hneg]; exact bot_le
    obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
    induction N using Nat.strong_induction_on with
    | _ N ihN =>
      have hlow : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ K := by
        intro m hm
        rcases lt_or_ge m 0 with hm0 | hm0
        · rw [W.positivity m hm0]; exact bot_le
        · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
          exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
      refine le_trans (grading_le_span_sup_O₂_inf W S hShom htop (N : ℤ)) ?_
      refine sup_le hSK ?_
      refine le_trans (O₂_inf_grading_le_span_deg W (N : ℤ)) ?_
      rw [Submodule.span_le]
      rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
      by_cases hg0 : W.smul a (-2) b = 0
      · rw [hg0]; exact Submodule.zero_mem _
      have hp0 : 0 ≤ p := by
        by_contra hc; push_neg at hc
        exact hg0 (by rw [show a = 0 by
          rw [W.positivity p hc, Submodule.mem_bot] at ha; exact ha, W.smul_zero_left])
      have hq0 : 0 ≤ q := by
        by_contra hc; push_neg at hc
        exact hg0 (by rw [show b = 0 by
          rw [W.positivity q hc, Submodule.mem_bot] at hb; exact hb, W.smul_zero_right])
      -- the weight-zero case: `a` is a multiple of `𝟙` and `𝟙₍₋₂₎b = 0`
      rcases eq_or_lt_of_le hp0 with hp | hp1
      · exfalso
        apply hg0
        have hmem : a ∈ W.grading (0 : ℤ) := by rw [hp]; exact ha
        rw [W.vacuum_grade, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, rfl⟩ := hmem
        rw [PreVertexAlgebra.smul_smul_left]
        have : W.smul W.vacuum (-2) b = 0 := by
          show mode (W.Y W.vacuum) (-2) b = 0
          rw [W.vacuum_Y, mode_one, if_neg (by norm_num)]
          rfl
        rw [this, smul_zero]
      -- the main case `wt a ≥ 1`
      have hpcast : ((p.toNat : ℕ) : ℤ) = p := by omega
      have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by rwa [hpcast]
      have hka : 1 ≤ p.toNat := by omega
      -- (α) `a[2k−2]b ∈ K` for every `k ≥ 1`
      have hpos : ∀ m : ℕ, vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b ∈ K := by
        intro m
        refine vSqZ_mem_of_lower W ha hb p.toNat _ K (fun d hd => hlow d ?_)
        have : (0 : ℤ) ≤ 2 * ((m : ℤ) + 1) - 2 := by omega
        omega
      -- (β) hence `a[−2]b ∈ K`, by condition (ii)
      have hneg2 : vSqZ W a p.toNat (-2) b ∈ K := by
        have hlaw := hD p.toNat hka a ha' b
        have hzero : ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            • qConv (zhuG (m + 1)) (D (vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b)) = 0 := by
          refine finsum_eq_zero_of_forall_eq_zero (fun m => ?_)
          have := hpos m
          rw [hK, LinearMap.mem_ker] at this
          rw [this, qConv_zero_right, smul_zero]
        rw [hzero, add_zero] at hlaw
        rw [hK, LinearMap.mem_ker]
        exact hlaw
      -- (γ) the defect is lower-degree, hence in `K`
      have hdef : sqDefect W a p.toNat b ∈ K :=
        sqDefect_mem_of_lower W ha hb hpq hp0 K hlow
      have hstep : W.smul a (-2) b = vSqZ W a p.toNat (-2) b - sqDefect W a p.toNat b := by
        rw [vSqZ_neg_two_eq W a p.toNat b]
        show W.smul a (-2) b = mode (W.Y a) (-2) b + sqDefect W a p.toNat b
          - sqDefect W a p.toNat b
        rw [add_sub_cancel_right]
        rfl
      rw [hstep]
      exact Submodule.sub_mem _ hneg2 hdef
  -- conclude
  ext x
  have hx : x ∈ Submodule.span ℂ {y : 𝒱 | IsHomog W y} := by
    rw [span_homog_eq_top]; trivial
  have hxK : x ∈ K := by
    refine (Submodule.span_le.mpr ?_) hx
    rintro y ⟨n, hy⟩
    exact hgrad n hy
  rw [hK, LinearMap.mem_ker] at hxK
  rw [hxK]
  rfl

/-- **Two blocks agreeing on the generators agree everywhere.**  The difference's condition
(ii) is carried explicitly, because `qConv` is only additive where the defining sums converge
(`qConv_add_apply`). -/
theorem eq_of_negTwoLaw_of_eqOn {S₁ S₂ : 𝒱 →ₗ[ℂ] FormalQSeries}
    (hdiff : NegTwoLaw W (S₁ - S₂)) (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (heq : ∀ x ∈ S, S₁ x = S₂ x) : S₁ = S₂ := by
  have h := eq_zero_of_negTwoLaw_of_vanish (S₁ - S₂) hdiff S hShom htop (fun x hx => by
    rw [LinearMap.sub_apply, heq x hx, sub_self])
  have := sub_eq_zero.mp h
  exact this

end Determinacy

/-! ## The packaged form for a `C₂`-cofinite VOA -/

section Packaged

variable {W : VertexOperatorAlgebra 𝒱}

/-- **Zhu's finiteness, algebraic core.**  For a `C₂`-cofinite VOA there is a *finite* family
`gen` of homogeneous vectors of positive weight such that every linear `D : 𝒱 → ℂ⟦q⟧` obeying
block condition (ii) and vanishing on `gen` and on `𝟙` vanishes identically.

So the genus-one blocks inject into `(Fin g ⊕ Unit) → ℂ⟦q⟧`: a block is pinned by `g + 1`
`q`-series.  (The remaining, analytic, half of Zhu Thm 5.3.2 bounds the space of possible series
by a modular linear differential equation.) -/
theorem blockDeterminedBy_of_C2Cofinite (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      ∀ D : 𝒱 →ₗ[ℂ] FormalQSeries, NegTwoLaw W D →
        (∀ i, D (gen i) = 0) → D W.vacuum = 0 → D = 0 := by
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨g, gen, wt, hwt, hgen, fun D hD hDgen hDvac => ?_⟩
  refine eq_zero_of_negTwoLaw_of_vanish D hD (Set.range gen ∪ {W.vacuum}) ?_ hdec ?_
  · rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  · rintro s (⟨i, rfl⟩ | hs)
    · exact hDgen i
    · rw [Set.mem_singleton_iff] at hs
      exact hs ▸ hDvac

end Packaged

end VOA
