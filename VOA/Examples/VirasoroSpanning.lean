/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroIsField

/-!
# The creation monomials span `VirUniv c`

The creation monomials `L₋ₙ₁₋₂ ⋯ L₋ₙₖ₋₂ |0⟩` (all modes `≤ -2`, since `L₋₁|0⟩ = 0`) span the
whole Virasoro vacuum module `VirUniv c = U(𝔙𝔦𝔯)/J(c)`.  This is the spanning half of PBW (linear
independence is NOT needed), proved `pbw`-free by straightening: any Virasoro generator applied to
a creation monomial stays in the span (commute it to the right where non-negative modes annihilate
`|0⟩`; the central cocycle acts by the scalar `c`), so the span is a `U(𝔙𝔦𝔯)`-submodule containing
`|0⟩`, hence everything by cyclicity `vac_cyclic`.

Mirror of `Foundations.AffineLie.negSpan_eq_top`, but for the single-generator Virasoro algebra.
`sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.VirModule

open VOA
open Module (End)
open LieAlgebra LieAlgebra.Extension UniversalEnvelopingAlgebra

variable (c : ℂ)

/-! ## §1  The commutator law for the `𝔙𝔦𝔯`-action. -/

/-- `x·(y·w) = y·(x·w) + ⁅x,y⁆·w` (since `virVacRho` is a Lie-algebra morphism). -/
theorem virVacRho_comm (x y : Virasoro) (w : VirUniv c) :
    virVacRho c x (virVacRho c y w)
      = virVacRho c y (virVacRho c x w) + virVacRho c ⁅x, y⁆ w := by
  have hml := (virVacRho c).map_lie x y
  rw [LieRing.of_associative_ring_bracket] at hml
  have happ := congrArg (fun A : End ℂ (VirUniv c) => A w) hml
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at happ
  rw [happ]; abel

/-! ## §2  The creation monomials and their `ℂ`-span. -/

/-- The **creation monomial** `L₋ₙ₁₋₂ ⋯ L₋ₙₖ₋₂ |0⟩` indexed by a list of exponents; all modes are
`≤ -2` (matching the vertex creation `ω₍₋ᵢ₋₁₎ = L₋ᵢ₋₂`). -/
noncomputable def negWordVir : List ℕ → VirUniv c
  | [] => vacVec c
  | n :: ws => Lop c (-(n : ℤ) - 2) (negWordVir ws)

/-- The empty creation word represents the vacuum; no Virasoro mode has yet acted. -/
@[simp] theorem negWordVir_nil : negWordVir c [] = vacVec c := rfl

/-- Prepending an index n applies the creation mode L_(-n-2) to the state represented by the remaining word. -/
theorem negWordVir_cons (n : ℕ) (ws : List ℕ) :
    negWordVir c (n :: ws) = Lop c (-(n : ℤ) - 2) (negWordVir c ws) := rfl

/-- The `ℂ`-span of all creation monomials. -/
noncomputable def negSpanVir : Submodule ℂ (VirUniv c) :=
  Submodule.span ℂ (Set.range (negWordVir c))

/-- Every creation word belongs to their linear span by its defining generating set. This supplies the base membership used in mode-stability and spanning arguments. -/
theorem negWordVir_mem (L : List ℕ) : negWordVir c L ∈ negSpanVir c :=
  Submodule.subset_span ⟨L, rfl⟩

/-- The creation modes `L₋ₙ₋₂` preserve `negSpan` (prepend another creation operator). -/
theorem negSpanVir_neg_stable (n : ℕ) {s : VirUniv c} (hs : s ∈ negSpanVir c) :
    Lop c (-(n : ℤ) - 2) s ∈ negSpanVir c := by
  induction hs using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; exact negWordVir_mem c (n :: ws)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-! ## §3  Straightening: every Virasoro generator stays in `negSpan`. -/

/-- **Straightening for `Lₘ`**: any mode `Lₘ` applied to a creation monomial stays in `negSpan`
(induction on the monomial, commuting `Lₘ` to the right where `Lₘ|0⟩ = 0` for `m ≥ -1`; the
central cocycle reduces via `c`). -/
theorem Lop_negWord (m : ℤ) (ws : List ℕ) :
    Lop c m (negWordVir c ws) ∈ negSpanVir c := by
  induction ws generalizing m with
  | nil =>
      rw [negWordVir_nil]
      rcases (by omega : m < -1 ∨ -1 ≤ m) with hm | hm
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) - 2 := ⟨(-m - 2).toNat, by omega⟩
        exact negWordVir_mem c [n]
      · rw [Lop_vacuum c hm]; exact Submodule.zero_mem _
  | cons i ws ih =>
      rw [negWordVir_cons]
      show virVacRho c (L m) (virVacRho c (L (-(i : ℤ) - 2)) (negWordVir c ws)) ∈ negSpanVir c
      rw [virVacRho_comm]
      apply Submodule.add_mem
      · exact negSpanVir_neg_stable c i (ih m)
      · rw [virasoro_bracket, map_add, LinearMap.add_apply]
        apply Submodule.add_mem
        · rw [map_smul, LinearMap.smul_apply]
          exact Submodule.smul_mem _ _ (ih (m + (-(i : ℤ) - 2)))
        · split_ifs with hcond
          · rw [map_smul, LinearMap.smul_apply, vac_acts_central, LinearMap.smul_apply,
              LinearMap.id_coe, id_eq]
            exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (negWordVir_mem c ws))
          · rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _

/-! ## §4  The Virasoro generators span `𝔙𝔦𝔯`; `negSpan` is a `U(𝔙𝔦𝔯)`-submodule. -/

/-- The standard generators of `𝔙𝔦𝔯`: all modes `Lₙ` together with the central `C`. -/
def gensVir : Set Virasoro := (Set.range fun n : ℤ => L n) ∪ {C}

/-- The generators span `𝔙𝔦𝔯` as a `ℂ`-vector space (the modes `Lₙ` span the Witt part, `C` the
central line). -/
theorem mem_span_gensVir (x : Virasoro) : x ∈ Submodule.span ℂ gensVir := by
  obtain ⟨⟨w, ζ⟩, rfl⟩ := (ofProd gfCocycle).surjective x
  have hwitt : ∀ w : Witt, ofProd gfCocycle (w, (0 : ℂ)) ∈ Submodule.span ℂ gensVir := by
    intro w
    induction w using Finsupp.induction with
    | zero => rw [show ((0 : Witt), (0 : ℂ)) = 0 from rfl, of_zero]; exact Submodule.zero_mem _
    | single_add n a w' _ _ ih =>
        have hsplit : ((Finsupp.single n a + w', (0 : ℂ)) : Witt × ℂ)
            = ((Finsupp.single n a, (0 : ℂ)) : Witt × ℂ) + (w', 0) := by
          rw [Prod.mk_add_mk, add_zero]
        rw [hsplit, of_add]
        refine Submodule.add_mem _ ?_ ih
        rw [show ofProd gfCocycle (Finsupp.single n a, (0 : ℂ)) = a • L n from by
            rw [L, Witt.gen, ← of_smul, Prod.smul_mk, Finsupp.smul_single, smul_eq_mul, mul_one,
              smul_zero]]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨n, rfl⟩))
  have hdecomp : ofProd gfCocycle (w, ζ) = ofProd gfCocycle (w, 0) + ζ • C := by
    simp only [C, ← of_smul, ← of_add, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [hdecomp]
  exact Submodule.add_mem _ (hwitt w)
    (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl)))

/-- Any element of `𝔙𝔦𝔯` applied to a creation monomial stays in `negSpan` (reduce to the
generators via `mem_span_gensVir`). -/
theorem virVacRho_negWord_mem (x : Virasoro) (ws : List ℕ) :
    virVacRho c x (negWordVir c ws) ∈ negSpanVir c := by
  induction (mem_span_gensVir x) using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨n, rfl⟩ | hy
      · exact Lop_negWord c n ws
      · rw [Set.mem_singleton_iff] at hy; subst hy
        rw [vac_acts_central, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
        exact Submodule.smul_mem _ _ (negWordVir_mem c ws)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ ha

/-- `negSpan` is stable under the whole `𝔙𝔦𝔯`-action. -/
theorem negSpan_rho_stable (x : Virasoro) {s : VirUniv c} (hs : s ∈ negSpanVir c) :
    virVacRho c x s ∈ negSpanVir c := by
  induction hs using Submodule.span_induction with
  | mem y hy => obtain ⟨ws, rfl⟩ := hy; exact virVacRho_negWord_mem c x ws
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

/-- `negSpan` is a `U(𝔙𝔦𝔯)`-submodule. -/
theorem negSpan_smul_stable (r : UVir) {s : VirUniv c} (hs : s ∈ negSpanVir c) :
    r • s ∈ negSpanVir c := by
  suffices H : ∀ p : TensorAlgebra ℂ Virasoro, ∀ t ∈ negSpanVir c, (mkU p) • t ∈ negSpanVir c by
    obtain ⟨p, rfl⟩ := mkU_surjective r
    exact H p s hs
  intro p
  induction p using TensorAlgebra.induction with
  | algebraMap a =>
      intro t ht; rw [AlgHom.commutes, algebraMap_smul UVir]; exact Submodule.smul_mem _ a ht
  | ι x => intro t ht; exact negSpan_rho_stable c x ht
  | mul p q hp hq => intro t ht; rw [map_mul, mul_smul]; exact hp _ (hq t ht)
  | add p q hp hq =>
      intro t ht; rw [map_add, add_smul]; exact Submodule.add_mem _ (hp t ht) (hq t ht)

/-! ## §5  The spanning theorem. -/

/-- **The creation monomials span** `VirUniv c`: `negSpan = ⊤` (i.e. `VirUniv c = U(𝔙𝔦𝔯₋)·|0⟩`), the
spanning half of PBW.  `pbw`-free — via cyclicity `vac_cyclic`. -/
theorem negSpanVir_eq_top : negSpanVir c = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hm : m ∈ Submodule.span UVir {vacVec c} := by rw [vac_cyclic]; trivial
  rw [Submodule.mem_span_singleton] at hm
  obtain ⟨r, rfl⟩ := hm
  exact negSpan_smul_stable c r (negWordVir_mem c [])

end VOA.VirModule
