/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockSlash
import VOA.Modularity.BlockSpace
import VOA.Modularity.BlockFiniteness
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic determinacy: a genus-one block is pinned by finitely many functions

`Modularity.BlockFiniteness` proved the *formal* half of Zhu's Theorem 5.3.2: a linear
`D : 𝒱 → ℂ⟦q⟧` obeying block condition (ii) and vanishing on a family spanning `𝒱` modulo
`C₂(𝒱)` vanishes identically.  This file runs the **same descent on the analytic side**, where
condition (ii) reads `F(a[−2]v)(z) = −Σ_k (2k−1)·G_{2k}(z)·F(a[2k−2]v)(z)` — an identity of
*functions* — so the induction takes place in the honest vanishing locus

  `blockKer F = {x | F x ≡ 0 on ℍ}`,

which is a genuine `ℂ`-submodule because an analytic block is linear in `v`.

* `IsAnalyticBlock.eq_zero_of_vanish` — the determinacy;
* `IsAnalyticBlock.determinedBy_of_C2Cofinite` — the packaged form: for a `C₂`-cofinite VOA an
  analytic block is pinned by its values on `g + 1` vectors.

## What this is and is not

This is the **injectivity** half of Zhu Thm 5.3.2: the block space embeds into
`(Fin g ⊕ Unit) → 𝒪(ℍ)`.  It is *not yet* finite-dimensionality: that needs the target of the
embedding cut down, i.e. the modular linear differential equation satisfied by each `F(genᵢ)`
(obtained from `IsGradedBlock.omega` by a Noetherian argument over `ℂ[E₄,E₆]`) together with
uniqueness for linear ODEs in the complex domain.  See the residual note at the end.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open Complex
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Determinacy

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

/-- **The vanishing locus of an analytic block** — a submodule, because a block is linear in `v`. -/
def blockKer (hF : IsAnalyticBlock W F) : Submodule ℂ 𝒱 where
  carrier := {x : 𝒱 | ∀ z ∈ imGT 0, F x z = 0}
  add_mem' := fun hx hy z hz => by rw [hF.addv, hx z hz, hy z hz, add_zero]
  zero_mem' := fun z _ => hF.zerov z
  smul_mem' := fun c _ hx z hz => by rw [hF.smulv, hx z hz, mul_zero]

@[simp] theorem mem_blockKer (hF : IsAnalyticBlock W F) (x : 𝒱) :
    x ∈ blockKer hF ↔ ∀ z ∈ imGT 0, F x z = 0 := Iff.rfl

/-- **Analytic determinacy.**  An analytic genus-one block vanishing on a homogeneous family
that spans `𝒱` modulo `C₂(𝒱)` vanishes identically on the upper half-plane. -/
theorem IsAnalyticBlock.eq_zero_of_vanish (hF : IsAnalyticBlock W F) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hvan : ∀ x ∈ S, ∀ z ∈ imGT 0, F x z = 0) : ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = 0 := by
  classical
  set K : Submodule ℂ 𝒱 := blockKer hF with hK
  have hSK : Submodule.span ℂ S ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    exact hvan x hx
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
      rcases eq_or_lt_of_le hp0 with hp | hp1
      · exfalso
        apply hg0
        have hmem : a ∈ W.grading (0 : ℤ) := by rw [hp]; exact ha
        rw [W.vacuum_grade, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, rfl⟩ := hmem
        rw [PreVertexAlgebra.smul_smul_left]
        have hvac : W.smul W.vacuum (-2) b = 0 := by
          show mode (W.Y W.vacuum) (-2) b = 0
          rw [W.vacuum_Y, mode_one, if_neg (by norm_num)]
          rfl
        rw [hvac, smul_zero]
      have hpcast : ((p.toNat : ℕ) : ℤ) = p := by omega
      have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by rwa [hpcast]
      have hka : 1 ≤ p.toNat := by omega
      have hpos : ∀ m : ℕ, vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b ∈ K := by
        intro m
        refine vSqZ_mem_of_lower W ha hb p.toNat _ K (fun d hd => hlow d ?_)
        have h2 : (0 : ℤ) ≤ 2 * ((m : ℤ) + 1) - 2 := by omega
        omega
      have hneg2 : vSqZ W a p.toNat (-2) b ∈ K := by
        intro z hz
        have hlaw := hF.negTwo p.toNat hka a ha' b z hz
        have hzero : ∑ᶠ m : ℕ, ((2 * (m + 1) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 1) z * F (vSqZ W a p.toNat (2 * (m + 1) - 2 : ℤ) b) z) = 0 := by
          refine finsum_eq_zero_of_forall_eq_zero (fun m => ?_)
          rw [hpos m z hz, mul_zero, mul_zero]
        rw [hzero, add_zero] at hlaw
        exact hlaw
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
  intro x
  have hx : x ∈ Submodule.span ℂ {y : 𝒱 | IsHomog W y} := by
    rw [span_homog_eq_top]; trivial
  have hxK : x ∈ K := by
    refine (Submodule.span_le.mpr ?_) hx
    rintro y ⟨n, hy⟩
    exact hgrad n hy
  exact hxK

/-- **Zhu's finiteness for analytic blocks, packaged.**  For a `C₂`-cofinite VOA there is a
*finite* family `gen` of homogeneous vectors of positive weight such that an analytic block
vanishing on `gen` and on `𝟙` vanishes identically: the block space embeds into
`(Fin g ⊕ Unit) → 𝒪(ℍ)`. -/
theorem IsAnalyticBlock.determinedBy_of_C2Cofinite (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      ∀ F : 𝒱 → ℂ → ℂ, IsAnalyticBlock W F →
        (∀ i, ∀ z ∈ imGT 0, F (gen i) z = 0) → (∀ z ∈ imGT 0, F W.vacuum z = 0) →
        ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = 0 := by
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨g, gen, wt, hwt, hgen, fun F hF hFgen hFvac => ?_⟩
  refine hF.eq_zero_of_vanish (Set.range gen ∪ {W.vacuum}) ?_ hdec ?_
  · rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  · rintro s (⟨i, rfl⟩ | hs)
    · exact hFgen i
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hFvac

/-- **Two analytic blocks agreeing on the determining family agree everywhere** — provided their
difference is again a block (the block conditions are `ℂ`-linear in `F`, but `IsAnalyticBlock`
bundles holomorphy, so the difference is carried explicitly). -/
theorem IsAnalyticBlock.eq_of_eqOn {F G : 𝒱 → ℂ → ℂ}
    (hdiff : IsAnalyticBlock W (fun v z => F v z - G v z)) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (heq : ∀ x ∈ S, ∀ z ∈ imGT 0, F x z = G x z) :
    ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = G x z := by
  intro x z hz
  have h := hdiff.eq_zero_of_vanish S hShom htop
    (fun s hs w hw => by rw [heq s hs w hw, sub_self]) x z hz
  exact sub_eq_zero.mp h

end Determinacy


/-! ## The Eisenstein-module refinement

The determinacy above throws away *how* a block is reconstructed from its values on the
`C₂`-generators.  Keeping track of it gives the statement the Noetherian step of Zhu Thm 5.3.2
actually consumes: since the `G₂`-term of condition (ii) is killed by condition (i)
(`IsAnalyticBlock.negTwo_tail`), the reconstruction uses only the **genuinely modular** `G_{2k}`,
`k ≥ 2`.  So every `F x` lies in the module generated by `F(gen)` over any ring of functions
containing those `G_{2k}` — in particular over `ℂ[E₄,E₆]`. -/

section Coeffs

variable {W : VertexOperatorAlgebra 𝒱} {F : 𝒱 → ℂ → ℂ}

/-- The vectors whose block value agrees on `ℍ` with an element of `M` — a submodule of `𝒱`,
because a block is linear in `v`. -/
def blockRep (hF : IsAnalyticBlock W F) (M : Submodule ℂ (ℂ → ℂ)) : Submodule ℂ 𝒱 where
  carrier := {x : 𝒱 | ∃ f ∈ M, ∀ z ∈ imGT 0, F x z = f z}
  add_mem' := by
    rintro x y ⟨f, hf, hfx⟩ ⟨g, hg, hgy⟩
    exact ⟨f + g, M.add_mem hf hg, fun z hz => by rw [hF.addv, hfx z hz, hgy z hz]; rfl⟩
  zero_mem' := ⟨0, M.zero_mem, fun z _ => by rw [hF.zerov]; rfl⟩
  smul_mem' := by
    rintro c x ⟨f, hf, hfx⟩
    exact ⟨c • f, M.smul_mem c hf, fun z hz => by rw [hF.smulv, hfx z hz]; rfl⟩

theorem mem_blockRep (hF : IsAnalyticBlock W F) (M : Submodule ℂ (ℂ → ℂ)) (x : 𝒱) :
    x ∈ blockRep hF M ↔ ∃ f ∈ M, ∀ z ∈ imGT 0, F x z = f z := Iff.rfl

/-- **The Eisenstein-module refinement of Zhu's determinacy.**

Let `M` be any `ℂ`-submodule of functions closed under multiplication by the *genuinely modular*
Eisenstein functions `G_{2k}`, `k ≥ 2`, and containing the values of a block `F` on a homogeneous
family spanning `𝒱` modulo `C₂(𝒱)`.  Then `M` contains the value of `F` on **every** vector.

Taking `M = ℂ[E₄,E₆]·{F(gen₁),…,F(gen_g),F(𝟙)}` this says: the whole of `F` is a **finitely
generated** module over the ring of modular forms.  That is exactly the input to the Noetherian
argument that produces Zhu's modular linear differential equation.  Note that `G₂` — which is
*not* modular — never appears, because condition (i) kills its term in condition (ii). -/
theorem IsAnalyticBlock.mem_eisensteinModule (hF : IsAnalyticBlock W F)
    (M : Submodule ℂ (ℂ → ℂ))
    (hMul : ∀ j : ℕ, 2 ≤ j → ∀ f ∈ M, (fun z => zhuGC j z * f z) ∈ M)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (hgen : ∀ s ∈ S, ∃ f ∈ M, ∀ z ∈ imGT 0, F s z = f z) :
    ∀ x : 𝒱, ∃ f ∈ M, ∀ z ∈ imGT 0, F x z = f z := by
  classical
  set K : Submodule ℂ 𝒱 := blockRep hF M with hK
  have hSK : Submodule.span ℂ S ≤ K := by
    rw [Submodule.span_le]
    intro x hx
    exact hgen x hx
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
        · obtain ⟨Mn, rfl⟩ : ∃ Mn : ℕ, m = (Mn : ℤ) := ⟨m.toNat, by omega⟩
          exact ihN Mn (by exact_mod_cast hm) (by exact_mod_cast hm0)
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
      rcases eq_or_lt_of_le hp0 with hp | hp1
      · exfalso
        apply hg0
        have hmem : a ∈ W.grading (0 : ℤ) := by rw [hp]; exact ha
        rw [W.vacuum_grade, Submodule.mem_span_singleton] at hmem
        obtain ⟨c, rfl⟩ := hmem
        rw [PreVertexAlgebra.smul_smul_left]
        have hvac : W.smul W.vacuum (-2) b = 0 := by
          show mode (W.Y W.vacuum) (-2) b = 0
          rw [W.vacuum_Y, mode_one, if_neg (by norm_num)]
          rfl
        rw [hvac, smul_zero]
      have hpcast : ((p.toNat : ℕ) : ℤ) = p := by omega
      have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by rwa [hpcast]
      have hka : 1 ≤ p.toNat := by omega
      -- (α) the tail vectors are of strictly lower degree
      have hpos : ∀ m : ℕ, vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b ∈ K := by
        intro m
        refine vSqZ_mem_of_lower W ha hb p.toNat _ K (fun d hd => hlow d ?_)
        have h2 : (2 : ℤ) ≤ 2 * ((m : ℤ) + 2) - 2 := by omega
        omega
      choose f hfM hfeq using fun m : ℕ => (mem_blockRep hF M _).mp (hpos m)
      -- (β) the tail is eventually zero, so the sum is finite
      obtain ⟨K₀, hK₀⟩ := vSqZ_tail_eventually_zero W a p.toNat b
      have hzero : ∀ m : ℕ, K₀ ≤ m → ∀ z ∈ imGT 0,
          ((2 * (m + 2) - 1 : ℕ) : ℂ)
            * (zhuGC (m + 2) z * F (vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b) z) = 0 := by
        intro m hm z _
        have hv0 : vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b = 0 := by
          have h := hK₀ (m + 1) (by omega)
          rw [show (2 * ((m : ℤ) + 2) - 2) = (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2) from by
            push_cast; ring]
          exact h
        rw [hv0, hF.zerov, mul_zero, mul_zero]
      have hneg2 : vSqZ W a p.toNat (-2) b ∈ K := by
        rw [hK, mem_blockRep]
        refine ⟨-∑ m ∈ Finset.range K₀,
          ((2 * (m + 2) - 1 : ℕ) : ℂ) • (fun z => zhuGC (m + 2) z * f m z), ?_, ?_⟩
        · exact Submodule.neg_mem _ (Submodule.sum_mem _ (fun m _ =>
            Submodule.smul_mem _ _ (hMul (m + 2) (by omega) (f m) (hfM m))))
        · intro z hz
          have hlaw := hF.negTwo_tail p.toNat hka ha' b hz
          have hsupp : (Function.support fun m : ℕ => ((2 * (m + 2) - 1 : ℕ) : ℂ)
              * (zhuGC (m + 2) z * F (vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b) z))
              ⊆ (Finset.range K₀ : Finset ℕ) := by
            intro m hm
            simp only [Function.mem_support, ne_eq] at hm
            simp only [Finset.coe_range, Set.mem_Iio]
            by_contra hc
            exact hm (hzero m (by omega) z hz)
          rw [finsum_eq_finsetSum_of_support_subset _ hsupp] at hlaw
          have hterm : ∀ m ∈ Finset.range K₀, ((2 * (m + 2) - 1 : ℕ) : ℂ)
              * (zhuGC (m + 2) z * F (vSqZ W a p.toNat (2 * (m + 2) - 2 : ℤ) b) z)
              = ((2 * (m + 2) - 1 : ℕ) : ℂ) * (zhuGC (m + 2) z * f m z) := by
            intro m _
            rw [hfeq m z hz]
          rw [Finset.sum_congr rfl hterm] at hlaw
          have hval : (-∑ m ∈ Finset.range K₀,
              ((2 * (m + 2) - 1 : ℕ) : ℂ) • (fun z => zhuGC (m + 2) z * f m z) : ℂ → ℂ) z
              = -∑ m ∈ Finset.range K₀,
                ((2 * (m + 2) - 1 : ℕ) : ℂ) * (zhuGC (m + 2) z * f m z) := by
            simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          rw [hval]
          linear_combination hlaw
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
  intro x
  have hx : x ∈ Submodule.span ℂ {y : 𝒱 | IsHomog W y} := by
    rw [span_homog_eq_top]; trivial
  have hxK : x ∈ K := by
    refine (Submodule.span_le.mpr ?_) hx
    rintro y ⟨n, hy⟩
    exact hgrad n hy
  exact (mem_blockRep hF M x).mp hxK

/-- **`∂`-stability of the Eisenstein module.**  Once `M` contains every value of the block
(`mem_eisensteinModule`), the `ω`-law *solves* for the Serre derivative,

  `∂_n F(v) = F(L[−2]v) − Σ_{k ≥ 2} G_{2k}·F(L[2k−2]v)`,

so `M` is stable under `∂`.  With `M = ℂ[E₄,E₆]·{F(gen), F(𝟙)}` this is the second half of the
Noetherian setup: a **finitely generated, `∂`-stable** module over a Noetherian ring, whose
ascending chain `⟨∂^{≤r}F(gen)⟩` must stabilise — which is Zhu's modular linear differential
equation. -/
theorem IsAnalyticBlock.serreDeriv_mem (hF : IsAnalyticBlock W F) (M : Submodule ℂ (ℂ → ℂ))
    (hMul : ∀ j : ℕ, 2 ≤ j → ∀ f ∈ M, (fun z => zhuGC j z * f z) ∈ M)
    (hall : ∀ x : 𝒱, ∃ f ∈ M, ∀ z ∈ imGT 0, F x z = f z)
    {n : ℤ} {v : 𝒱} (hv : v ∈ sqWeightSpace W (n : ℂ)) :
    ∃ f ∈ M, ∀ z ∈ imGT 0, serreDerivC n (F v) z = f z := by
  classical
  obtain ⟨K₀, hK₀⟩ := Lsq_tail_eventually_zero W v
  obtain ⟨f0, hf0M, hf0⟩ := hall (Lsq W (-2) v)
  choose f hfM hfeq using fun m : ℕ => hall (Lsq W (2 * (m + 2) - 2 : ℤ) v)
  refine ⟨f0 - ∑ m ∈ Finset.range K₀, (fun w => zhuGC (m + 2) w * f m w), ?_, ?_⟩
  · exact M.sub_mem hf0M
      (Submodule.sum_mem _ (fun m _ => hMul (m + 2) (by omega) (f m) (hfM m)))
  · intro z hz
    have hlaw := hF.omega_serre hv hz
    have hzero : ∀ m : ℕ, K₀ ≤ m →
        zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z = 0 := by
      intro m hm
      have hv0 : Lsq W (2 * (m + 2) - 2 : ℤ) v = 0 := by
        have h := hK₀ (m + 1) (by omega)
        rw [show (2 * ((m : ℤ) + 2) - 2) = (2 * (((m + 1 : ℕ) : ℤ) + 1) - 2) from by push_cast; ring]
        exact h
      rw [hv0, hF.zerov, mul_zero]
    have hsupp : (Function.support fun m : ℕ =>
        zhuGC (m + 2) z * F (Lsq W (2 * (m + 2) - 2 : ℤ) v) z)
        ⊆ (Finset.range K₀ : Finset ℕ) := by
      intro m hm
      simp only [Function.mem_support, ne_eq] at hm
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hc
      exact hm (hzero m (by omega))
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp,
      Finset.sum_congr rfl (fun m _ => by rw [hfeq m z hz])] at hlaw
    have hval : ((f0 - ∑ m ∈ Finset.range K₀, (fun w => zhuGC (m + 2) w * f m w)) : ℂ → ℂ) z
        = f0 z - ∑ m ∈ Finset.range K₀, zhuGC (m + 2) z * f m z := by
      simp only [Pi.sub_apply, Finset.sum_apply]
    rw [hval, ← hf0 z hz]
    linear_combination -hlaw

/-- **The block is an `R`-linear combination of its values on the `C₂`-generators**, for any
`ℂ`-subalgebra `R` of functions containing the modular `G_{2k}`, `k ≥ 2` (e.g. `ℂ[E₄,E₆]`, or the
*differential* subalgebra they generate — which is automatically `∂`-stable).  This is
`mem_eisensteinModule` packaged as a genuine finite-generation statement. -/
theorem IsAnalyticBlock.mem_span_eisenstein (hF : IsAnalyticBlock W F)
    (R : Subalgebra ℂ (ℂ → ℂ)) (hR : ∀ j : ℕ, 2 ≤ j → zhuGC j ∈ R)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) :
    ∀ x : 𝒱, ∃ f ∈ Submodule.span R (F '' S), ∀ z ∈ imGT 0, F x z = f z := by
  classical
  set N : Submodule R (ℂ → ℂ) := Submodule.span R (F '' S) with hN
  have hmain := hF.mem_eisensteinModule (N.restrictScalars ℂ) ?_ S hShom htop ?_
  · intro x
    obtain ⟨f, hf, hfx⟩ := hmain x
    exact ⟨f, hf, hfx⟩
  · intro j hj f hf
    have hfN : f ∈ N := hf
    have hsm : (fun z => zhuGC j z * f z) = (⟨zhuGC j, hR j hj⟩ : R) • f := rfl
    show (fun z => zhuGC j z * f z) ∈ N
    rw [hsm]
    exact N.smul_mem _ hfN
  · intro s hs
    exact ⟨F s, Submodule.subset_span ⟨s, hs, rfl⟩, fun _ _ => rfl⟩

end Coeffs

/-! ## The identity theorem on `ℍ`

`imGT 0` is open and **connected** (`isPreconnected_imGT` — it is convex), so a holomorphic
function on it is determined by its germ at any one point.  Combined with
`IsAnalyticBlock.eq_of_eqOn` this is the step that turns "finitely many Taylor coefficients" into
"finite-dimensional": a block is pinned by `g + 1` functions, and each of those is pinned by its
Taylor expansion at a single `τ₀ ∈ ℍ`. -/

section Identity

/-- **The identity theorem on the upper half-plane.**  Two functions holomorphic on `imGT 0`
that agree near one point of it agree on all of it. -/
theorem eqOn_imGT_of_eventuallyEq {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (imGT 0))
    (hg : DifferentiableOn ℂ g (imGT 0)) {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0)
    (heq : f =ᶠ[nhds z₀] g) : Set.EqOn f g (imGT 0) := by
  intro z hz
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hf.analyticOnNhd (isOpen_imGT 0)) (hg.analyticOnNhd (isOpen_imGT 0))
    (isPreconnected_imGT 0) hz₀ heq hz

variable {W : VertexOperatorAlgebra 𝒱} {F G : 𝒱 → ℂ → ℂ}

/-- **A genus-one block is determined by its germs at a single point of `ℍ`.**  With
`determinedBy_of_C2Cofinite` this says: for a `C₂`-cofinite VOA a block is pinned by the germs at
one `τ₀` of the `g + 1` functions `F(gen₁),…,F(gen_g),F(𝟙)` — the finiteness statement that a
modular linear differential equation would turn into a dimension bound. -/
theorem IsAnalyticBlock.eq_of_germ_eq (hF : IsAnalyticBlock W F) (hG : IsAnalyticBlock W G)
    (hdiff : IsAnalyticBlock W (fun v z => F v z - G v z)) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) (hgerm : ∀ x ∈ S, F x =ᶠ[nhds z₀] G x) :
    ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = G x z :=
  IsAnalyticBlock.eq_of_eqOn hdiff S hShom htop
    (fun x hx z hz => eqOn_imGT_of_eventuallyEq (hF.holo x) (hG.holo x) hz₀ (hgerm x hx) hz)

/-- **Two blocks agreeing on the determining family agree everywhere** — the `hdiff`
hypothesis of `eq_of_eqOn` is *discharged*, because the blocks form a `ℂ`-subspace
(`Modularity.BlockSpace.analyticBlocks`). -/
theorem IsAnalyticBlock.eq_of_eqOn' (hF : IsAnalyticBlock W F) (hG : IsAnalyticBlock W G)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    (heq : ∀ x ∈ S, ∀ z ∈ imGT 0, F x z = G x z) :
    ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = G x z :=
  IsAnalyticBlock.eq_of_eqOn (hF.sub hG) S hShom htop heq

/-- **A genus-one block is determined by finitely many germs at a single `τ₀ ∈ ℍ`** —
unconditional form. -/
theorem IsAnalyticBlock.eq_of_germ_eq' (hF : IsAnalyticBlock W F) (hG : IsAnalyticBlock W G)
    (S : Set 𝒱) (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W)
    {z₀ : ℂ} (hz₀ : z₀ ∈ imGT 0) (hgerm : ∀ x ∈ S, F x =ᶠ[nhds z₀] G x) :
    ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = G x z :=
  hF.eq_of_eqOn' hG S hShom htop
    (fun x hx z hz => eqOn_imGT_of_eventuallyEq (hF.holo x) (hG.holo x) hz₀ (hgerm x hx) hz)

/-- **Zhu's finiteness as an injectivity statement on the block SPACE.**  For a `C₂`-cofinite
VOA the linear map `𝔅 → (Fin g ⊕ Unit) → 𝒪(ℍ)`, `F ↦ (F(genᵢ), F(𝟙))`, is injective. -/
theorem analyticBlocks_injective_of_C2Cofinite (hC2 : C2Cofinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      ∀ F ∈ analyticBlocks W, ∀ G ∈ analyticBlocks W,
        (∀ i, ∀ z ∈ imGT 0, F (gen i) z = G (gen i) z) →
        (∀ z ∈ imGT 0, F W.vacuum z = G W.vacuum z) →
        ∀ (x : 𝒱), ∀ z ∈ imGT 0, F x z = G x z := by
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  refine ⟨g, gen, wt, hwt, hgen, fun F hF G hG hFG hvac => ?_⟩
  refine IsAnalyticBlock.eq_of_eqOn' hF hG (Set.range gen ∪ {W.vacuum}) ?_ hdec ?_
  · rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  · rintro s (⟨i, rfl⟩ | hs)
    · exact hFG i
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hvac

end Identity

/-! ## Residual toward Zhu Thm 5.3.2 (finite-dimensionality)

Proved here:

* `analyticBlocks_injective_of_C2Cofinite` — the block **space** (`Modularity.BlockSpace`) injects
  into `(Fin g ⊕ Unit) → 𝒪(ℍ)`;
* `IsAnalyticBlock.mem_eisensteinModule` / `mem_span_eisenstein` — **finite generation**: every
  value of a block lies in the `R`-span of its values on the `C₂`-generators, for any subalgebra
  `R` of functions containing the *modular* `G_{2k}`, `k ≥ 2`;
* `IsAnalyticBlock.serreDeriv_mem` — that module is **`∂`-stable**;
* `eqOn_imGT_of_eventuallyEq` / `eq_of_germ_eq'` — a block is pinned by finitely many **germs** at
  one point of `ℍ` (identity theorem on the connected `imGT 0`).

**⚠ Remark.**  Noetherianity of `ℂ[E₄,E₆]` — and hence the
structure theorem for level-one modular forms, which Mathlib lacks — is **not** actually needed:

* Take `R` to be the *differential* `ℂ`-subalgebra of `𝒪(ℍ)` generated by `{G_{2k} : k ≥ 2}`.  It
  contains the `G_{2k}` (so `mem_span_eisenstein` applies) and is `∂`-stable **by construction**,
  so no Ramanujan identity and no generation theorem are required.
* `R` is automatically an integral domain: it sits inside `𝒪(imGT 0)`, and `imGT 0` is connected
  (`isPreconnected_imGT`), so the identity theorem makes that ring a domain.
* Over a nontrivial *commutative* ring Mathlib supplies `StrongRankCondition`, hence
  `linearIndependent_le_span`: in a module spanned by `g + 1` elements, no `g + 2` elements are
  linearly independent.  Applied to `∂^{≤ g+1} F(𝟙)` inside the module of `mem_span_eisenstein`,
  this is exactly Zhu's **modular linear differential equation**, of order `≤ g + 1`.

So the honest remaining gap is the *single* step

  **uniqueness for a linear ODE with holomorphic coefficients** — a solution of
  `∂ʳ f = Σ_{j<r} c_j ∂ʲ f` whose first `r` derivatives vanish at one point of `ℍ` vanishes
  identically (Taylor recursion, then `eqOn_imGT_of_eventuallyEq`)

together with the routine bookkeeping that turns the linear relation into that ODE.  None of it is
needed for `Modularity.RhoS.zhu_modularity_of_blockSpanned`, which consumes the spanning statement
directly rather than a dimension count.
-/

end VOA
