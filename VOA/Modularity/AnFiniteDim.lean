/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.ZhuAlgebraFinite
import VOA.Modules.ZhuVermaAn

/-!
# `C_{2n+2}`-cofiniteness ⟹ `dim A_n(𝒱) < ∞`

`Modularity.ZhuAlgebraFinite.finiteDimensional_A_of_C2Cofinite` proves the `n = 0` case from
`C₂`-cofiniteness.  This file runs the *same* induction at level `n` and pins down exactly which
cofiniteness it needs.

The mechanism is `circ_homogeneous`: for `a ∈ 𝒱ₖ`,

  `a ∘ₙ b = ∑_{i=0}^{k+n} C(k+n, i)·a₍ᵢ₋₂ₙ₋₂₎b ∈ O_n(𝒱)`,

whose `i = 0` term is `a₍₋₂ₙ₋₂₎b` and whose `i ≥ 1` terms have **strictly lower** conformal weight
(`wt a₍ᵢ₋₂ₙ₋₂₎b = k + wt b + 2n + 1 − i`).  So modulo `O_n(𝒱)` the whole of `C_{2n+2}(𝒱)` is
absorbed into lower degrees.

⚠ **This is why the `n = 0` proof does not generalize to `C₂`-cofiniteness.**  The absorbed family
is `C_{2n+2}(𝒱) = span{a₍₋₂ₙ₋₂₎b}`, *not* `C₂(𝒱)`; and since
`a₍₋ₘ₋₁₎b = (1/m)·(L(−1)a)₍₋ₘ₎b` gives `C_{m+1}(𝒱) ⊆ C_m(𝒱)`, one has
`dim 𝒱/C_{2n+2} ≥ dim 𝒱/C₂`, so `C₂`-cofiniteness supplies nothing here.  The missing implication
`C₂`-cofinite ⟹ `C_m`-cofinite is Gaberdiel–Neitzke Prop. 8 and is **not** in the repo.

## Main results

* `CGen` — `C_M(𝒱) := span{u₍M₎v}`, with `CGen W (-2) = O₂ W`;
* `CGen_eq_span_homGen`, `CGen_inf_grading_le_span_deg`, `grading_le_span_sup_CGen_inf` — the
  graded machinery, parametric in the mode index;
* `smul_negM_mem_of_lower_On` — the one-step absorption at level `n`;
* `grading_le_span_sup_On`, `span_sup_On_eq_top`, `exists_finset_span_sup_On`;
* `finiteDimensional_An_of_cofinite` — `dim 𝒱/C_{2n+2} < ∞ ⟹ dim A_n(𝒱) < ∞`.

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `C_M(𝒱)`, parametric in the mode index -/

/-- `C_M(𝒱) := span{u₍M₎v}`.  At `M = −2` this is Zhu's `C₂(𝒱) = O₂(𝒱)`. -/
def CGen (W : VertexOperatorAlgebra 𝒱) (M : ℤ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u v : 𝒱, x = W.smul u M v}

theorem CGen_neg_two (W : VertexOperatorAlgebra 𝒱) : CGen W (-2) = O₂ W := rfl

/-- The homogeneous generators of `C_M(𝒱)`. -/
def CGenHom (W : VertexOperatorAlgebra 𝒱) (M : ℤ) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ W.grading p ∧ b ∈ W.grading q ∧ x = W.smul a M b}

/-- The homogeneous generators of *exact* degree `n`. -/
def CGenHomDeg (W : VertexOperatorAlgebra 𝒱) (M n : ℤ) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ W.grading p ∧ b ∈ W.grading q ∧ p + q - M - 1 = n ∧
    x = W.smul a M b}

theorem cgen_mem_grading (W : VertexOperatorAlgebra 𝒱) {M p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) :
    W.smul a M b ∈ W.grading (p + q - M - 1) :=
  W.smul_mem_grading ha hb M

theorem cgenHom_homog (W : VertexOperatorAlgebra 𝒱) {M : ℤ} {g : 𝒱}
    (hg : g ∈ CGenHom W M) : IsHomog W g := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  exact ⟨p + q - M - 1, cgen_mem_grading W ha hb⟩

theorem cgenHomDeg_mem_grading (W : VertexOperatorAlgebra 𝒱) {M n : ℤ} {g : 𝒱}
    (hg : g ∈ CGenHomDeg W M n) : g ∈ W.grading n := by
  obtain ⟨p, q, a, b, ha, hb, hpq, rfl⟩ := hg
  rw [← hpq]; exact cgen_mem_grading W ha hb

theorem cgen_homA_mem_span (W : VertexOperatorAlgebra 𝒱) (M : ℤ) {p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading p) (b : 𝒱) :
    W.smul a M b ∈ Submodule.span ℂ (CGenHom W M) := by
  have hb : b ∈ Submodule.span ℂ {x | IsHomog W x} := by rw [span_homog_eq_top]; trivial
  refine Submodule.span_induction
    (p := fun b _ => W.smul a M b ∈ Submodule.span ℂ (CGenHom W M)) ?_ ?_ ?_ ?_ hb
  · rintro y ⟨q, hq⟩
    exact Submodule.subset_span ⟨p, q, a, y, ha, hq, rfl⟩
  · simp
  · intro y z _ _ hy hz
    rw [W.smul_add_right]; exact (Submodule.span ℂ (CGenHom W M)).add_mem hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]; exact (Submodule.span ℂ (CGenHom W M)).smul_mem c hy

theorem cgen_mem_span (W : VertexOperatorAlgebra 𝒱) (M : ℤ) (a b : 𝒱) :
    W.smul a M b ∈ Submodule.span ℂ (CGenHom W M) := by
  have ha : a ∈ Submodule.span ℂ {x | IsHomog W x} := by rw [span_homog_eq_top]; trivial
  refine Submodule.span_induction
    (p := fun a _ => W.smul a M b ∈ Submodule.span ℂ (CGenHom W M)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨p, hp⟩; exact cgen_homA_mem_span W M hp b
  · simp
  · intro y z _ _ hy hz
    rw [W.smul_add_left]; exact (Submodule.span ℂ (CGenHom W M)).add_mem hy hz
  · intro c y _ hy
    rw [W.smul_smul_left]; exact (Submodule.span ℂ (CGenHom W M)).smul_mem c hy

/-- **`C_M(𝒱)` is graded.** -/
theorem CGen_eq_span_homGen (W : VertexOperatorAlgebra 𝒱) (M : ℤ) :
    CGen W M = Submodule.span ℂ (CGenHom W M) := by
  apply le_antisymm
  · rw [CGen, Submodule.span_le]; rintro x ⟨a, b, rfl⟩; exact cgen_mem_span W M a b
  · rw [Submodule.span_le]; rintro x ⟨p, q, a, b, ha, hb, rfl⟩
    exact Submodule.subset_span ⟨a, b, rfl⟩

theorem piHom_maps_CGen (W : VertexOperatorAlgebra 𝒱) (M n : ℤ) {x : 𝒱} (hx : x ∈ CGen W M) :
    piHom W n x ∈ CGen W M := by
  rw [CGen_eq_span_homGen] at hx ⊢
  exact piHom_maps_span_homog W n (CGenHom W M) (fun g hg => cgenHom_homog W hg) hx

/-- **Graded spanning.** -/
theorem grading_le_span_sup_CGen_inf (W : VertexOperatorAlgebra 𝒱) (M : ℤ) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ CGen W M) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ (CGen W M ⊓ W.grading n) := by
  intro x hx
  have hxtop : x ∈ Submodule.span ℂ S ⊔ CGen W M := htop ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hxtop
  obtain ⟨a, ha, b, hb, rfl⟩ := hxtop
  have hpix : piHom W n (a + b) = a + b := piHom_of_mem W hx
  rw [map_add] at hpix
  have hpa_S : piHom W n a ∈ Submodule.span ℂ S := piHom_maps_span_homog W n S hShom ha
  have hpb_O : piHom W n b ∈ CGen W M := piHom_maps_CGen W M n hb
  have hpb_g : piHom W n b ∈ W.grading n := piHom_mem W n b
  rw [← hpix]
  exact Submodule.add_mem_sup hpa_S ⟨hpb_O, hpb_g⟩

theorem piHom_cgenHom_mem (W : VertexOperatorAlgebra 𝒱) (M n : ℤ) {g : 𝒱}
    (hg : g ∈ CGenHom W M) : piHom W n g ∈ Submodule.span ℂ (CGenHomDeg W M n) := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  by_cases hd : p + q - M - 1 = n
  · rw [piHom_of_mem W (by rw [← hd]; exact cgen_mem_grading W ha hb)]
    exact Submodule.subset_span ⟨p, q, a, b, ha, hb, hd, rfl⟩
  · rw [piHom_of_mem_ne W (k := p + q - M - 1) (by omega) (cgen_mem_grading W ha hb)]
    exact (Submodule.span ℂ (CGenHomDeg W M n)).zero_mem

/-- **Graded reduction of `C_M ⊓ 𝒱ₙ`.** -/
theorem CGen_inf_grading_le_span_deg (W : VertexOperatorAlgebra 𝒱) (M n : ℤ) :
    CGen W M ⊓ W.grading n ≤ Submodule.span ℂ (CGenHomDeg W M n) := by
  intro x hx
  obtain ⟨hxO, hxg⟩ := hx
  rw [CGen_eq_span_homGen] at hxO
  rw [← piHom_of_mem W hxg]
  refine Submodule.span_induction
    (p := fun y _ => piHom W n y ∈ Submodule.span ℂ (CGenHomDeg W M n)) ?_ ?_ ?_ ?_ hxO
  · intro g hg; exact piHom_cgenHom_mem W M n hg
  · simp only [map_zero]; exact (Submodule.span ℂ (CGenHomDeg W M n)).zero_mem
  · intro y z _ _ hy hz; rw [map_add]
    exact (Submodule.span ℂ (CGenHomDeg W M n)).add_mem hy hz
  · intro c y _ hy; rw [map_smul]
    exact (Submodule.span ℂ (CGenHomDeg W M n)).smul_mem c hy

/-! ## The level-`n` absorption and the degree induction -/

/-- **The one-step absorption at level `n`.**  For homogeneous `a ∈ 𝒱ₚ` (`p ≥ 0`) and `b ∈ 𝒱_q`,
the vector `a₍₋₂ₙ₋₂₎b` lies in any subspace containing `O_n(𝒱)` and every grade strictly below
`p + q + 2n + 1`. -/
theorem smul_negM_mem_of_lower_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hp : 0 ≤ p)
    (T : Submodule ℂ 𝒱) (hO : On W n ≤ T)
    (hT : ∀ m : ℤ, m < p + q + 2 * (n : ℤ) + 1 → W.grading m ≤ T) :
    W.smul a (-2 * (n : ℤ) - 2) b ∈ T := by
  classical
  obtain ⟨K, rfl⟩ : ∃ K : ℕ, p = (K : ℤ) := ⟨p.toNat, by omega⟩
  have hcirc : circ W n a b ∈ T := hO (circ_mem_On W n a b)
  have hexp := circ_homogeneous W n ha b
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ((K : ℤ) + (n : ℤ)).toNat = R := ⟨_, rfl⟩
  rw [hR, Finset.sum_range_succ'] at hexp
  have htail : ∑ i ∈ Finset.range R,
      cbz ((K : ℤ) + (n : ℤ)) ((i : ℕ) + 1 : ℕ) • W.smul a (((i + 1 : ℕ) : ℤ) - 2 * (n : ℤ) - 2) b
        ∈ T := by
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    refine hT _ ?_ (cgen_mem_grading W ha hb)
    push_cast
    omega
  have hzero : cbz ((K : ℤ) + (n : ℤ)) ((0 : ℕ) : ℤ)
      • W.smul a (((0 : ℕ) : ℤ) - 2 * (n : ℤ) - 2) b ∈ T := by
    have := Submodule.sub_mem _ hcirc htail
    rwa [hexp, add_sub_cancel_left] at this
  rw [Nat.cast_zero, cbz_zero, one_smul, show ((0 : ℤ) - 2 * (n : ℤ) - 2)
    = (-2 * (n : ℤ) - 2) by ring] at hzero
  exact hzero

/-- **The degree induction at level `n`.** -/
theorem grading_le_span_sup_On (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ S ⊔ CGen W (-2 * (n : ℤ) - 2)) (N : ℤ) :
    W.grading N ≤ Submodule.span ℂ S ⊔ On W n := by
  classical
  set T : Submodule ℂ 𝒱 := Submodule.span ℂ S ⊔ On W n with hTdef
  have hO : On W n ≤ T := le_sup_right
  rcases lt_or_ge N 0 with hneg | hnn
  · rw [W.positivity N hneg]; exact bot_le
  obtain ⟨M, rfl⟩ : ∃ M : ℕ, N = (M : ℤ) := ⟨N.toNat, by omega⟩
  induction M using Nat.strong_induction_on with
  | _ M ihM =>
    have hT : ∀ m : ℤ, m < (M : ℤ) → W.grading m ≤ T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · rw [W.positivity m hm0]; exact bot_le
      · obtain ⟨M', rfl⟩ : ∃ M' : ℕ, m = (M' : ℤ) := ⟨m.toNat, by omega⟩
        exact ihM M' (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (grading_le_span_sup_CGen_inf W _ S hShom htop (M : ℤ)) ?_
    refine sup_le le_sup_left ?_
    refine le_trans (CGen_inf_grading_le_span_deg W _ (M : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g ⟨p, q, a, b, ha, hb, hpq, rfl⟩
    by_cases hg0 : W.smul a (-2 * (n : ℤ) - 2) b = 0
    · rw [hg0]; exact Submodule.zero_mem _
    have hp0 : 0 ≤ p := by
      by_contra hc; push_neg at hc
      exact hg0 (by rw [show a = 0 by
        rw [W.positivity p hc, Submodule.mem_bot] at ha; exact ha, W.smul_zero_left])
    exact smul_negM_mem_of_lower_On W n ha hb hp0 T hO (fun m hm => hT m (by omega))

/-- Span form. -/
theorem span_sup_On_eq_top (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ S ⊔ CGen W (-2 * (n : ℤ) - 2)) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ On W n := by
  refine le_antisymm ?_ le_top
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_span_sup_On W n S hShom htop m hx

/-- **`C_{2n+2}`-cofinite ⟹ `dim A_n(𝒱) < ∞`.**  The level-`n` analogue of
`finiteDimensional_A_of_C2Cofinite`, with the cofiniteness input it actually needs. -/
theorem finiteDimensional_An_of_cofinite (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (S : Finset 𝒱)
    (hShom : ∀ s ∈ (S : Set 𝒱), IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱)
      = Submodule.span ℂ (S : Set 𝒱) ⊔ CGen W (-2 * (n : ℤ) - 2)) :
    FiniteDimensional ℂ (An W n) ∧ Module.finrank ℂ (An W n) ≤ S.card :=
  finiteDimensional_and_finrank_quot_le_of_span_sup S (span_sup_On_eq_top W n _ hShom htop)

end VOA
