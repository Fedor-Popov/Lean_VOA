/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Core.DongSuperNeg
import VOA.Core.ReconstructionExistence
import VOA.Core.FieldOps

/-!
# Super reconstruction: building a vertex superalgebra from local fields

The existence direction for the super case — the analogue of
`Core.ReconstructionExistence.reconstruct`.  With `dong_negε` in hand this is the last structural
piece before a `SuperVertexAlgebra` can be *built* rather than merely defined.

## What changes, and what does not

Almost nothing changes.  The two observations that make this cheap:

* **Standalone Goddard uniqueness is `ε`-blind.**  `goddard_zero_at` works by rewriting
  `A p (Gb q vac)` as the bracket applied to the vacuum, which is legitimate precisely because
  `A p vac = 0` — and that same hypothesis kills the `ε •` term in `bracketDistε`.  So the
  `ε`-twisted proof is the bosonic one with a `smul_zero` inserted.
* **The `ε` is constant across a parity-homogeneous linear combination.**  Locality bookkeeping
  (`add_left`, `sum_left`, `smul`, …) therefore ports verbatim at fixed `ε`; only the final
  statement has to track which parity each state came from.

## What is here

`Localε` algebra (§1), the standalone super Goddard uniqueness (§2), and `reconstructε` (§3):
from a parity-graded family of pairwise `koszul`-local creating fields, a linear `YA` with
`YA (st i) = fld i`, fields, `koszul`-locality on parity-homogeneous states, creation, and
translation covariance.
-/

namespace VOA

open Module (End)
open VOA.Reconstruction

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-! ## §1  `Localε` algebra at fixed `ε` -/

/-- `ε`-locality on the left is preserved by addition. -/
theorem Localε.add_left {ε : ℂ} {a b g : FormalDist (End ℂ V)}
    (h1 : Localε ε a g) (h2 : Localε ε b g) : Localε ε (a + b) g := by
  obtain ⟨N1, hN1⟩ := h1
  obtain ⟨N2, hN2⟩ := h2
  refine ⟨max N1 N2, ?_⟩
  rw [bracketDistε_add_left, map_add, mulBySubPow_mono₂ (le_max_left N1 N2) hN1,
    mulBySubPow_mono₂ (le_max_right N1 N2) hN2, add_zero]

/-- The zero field is `ε`-local with everything on the left. -/
theorem Localε.zero_left (ε : ℂ) (g : FormalDist (End ℂ V)) :
    Localε ε (0 : FormalDist (End ℂ V)) g := by
  refine localε_of_bracketDistε_eq_zero ?_
  apply FormalDist₂.ext; intro m n
  rw [bracketDistε_apply]
  show (0 : End ℂ V) * g n - ε • (g n * (0 : End ℂ V)) = (0 : End ℂ V)
  rw [zero_mul, mul_zero, smul_zero, sub_zero]

/-- `ε`-locality is invariant under scaling on the left. -/
theorem Localε.smul_left (ε : ℂ) (c : ℂ) {F G : FormalDist (End ℂ V)} (h : Localε ε F G) :
    Localε ε (c • F) G := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  have he : bracketDistε ε (c • F) G = c • bracketDistε ε F G := by
    apply FormalDist₂.ext; intro m n
    show (c • F m) * G n - ε • (G n * (c • F m)) = c • (F m * G n - ε • (G n * F m))
    rw [smul_sub, smul_mul_assoc, mul_smul_comm, smul_comm ε c]
  rw [he, map_smul, hN, smul_zero]

/-- A finite `Finset`-sum of fields each `ε`-local with `g` is `ε`-local with `g`. -/
theorem Localε.sum_left {ι : Type*} (ε : ℂ) (s : Finset ι) (f : ι → FormalDist (End ℂ V))
    (g : FormalDist (End ℂ V)) (h : ∀ i ∈ s, Localε ε (f i) g) :
    Localε ε (∑ i ∈ s, f i) g := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact Localε.zero_left ε g
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Localε.add_left (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **`ε`-locality is symmetric when `ε² = 1`** — the super case.  From `bracketDistε_swap`,
`[a,b]_ε = -(ε • swap [b,a]_{ε⁻¹})`, and `ε⁻¹ = ε`. -/
theorem Localε.symm {ε : ℂ} (hε2 : ε * ε = 1) {a b : FormalDist (End ℂ V)}
    (h : Localε ε a b) : Localε ε b a := by
  have hεne : ε ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hε2; exact one_ne_zero hε2.symm
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  -- `swap₂ [b,a]_ε = (-ε) • [a,b]_ε`, using `ε² = 1` once.
  have hsw : swap₂ (bracketDistε ε b a) = (-ε) • bracketDistε ε a b := by
    apply FormalDist₂.ext; intro m n
    show b n * a m - ε • (a m * b n) = ((-ε) • bracketDistε ε a b) m n
    show b n * a m - ε • (a m * b n) = (-ε) • (a m * b n - ε • (b n * a m))
    have h1 : (-ε) • (a m * b n - ε • (b n * a m))
        = -(ε • (a m * b n)) + (b n * a m) := by
      simp only [smul_sub, smul_smul, neg_mul, neg_smul, sub_neg_eq_add, hε2, one_smul]
    rw [h1]
    abel
  have hz : mulBySubPow N (swap₂ (bracketDistε ε b a)) = 0 := by
    rw [hsw, map_smul, hN, smul_zero]
  have hback := mulBySubPow_swap_eq_zero N (swap₂ (bracketDistε ε b a)) hz
  rwa [show swap₂ (swap₂ (bracketDistε ε b a)) = bracketDistε ε b a from rfl] at hback

/-- `ε`-locality is invariant under scaling on the right. -/
theorem Localε.smul_right {ε : ℂ} (hε2 : ε * ε = 1) (c : ℂ) {F G : FormalDist (End ℂ V)}
    (h : Localε ε F G) : Localε ε F (c • G) :=
  Localε.symm hε2 (Localε.smul_left ε c (Localε.symm hε2 h))

/-- A finite `Finset`-sum on the right. -/
theorem Localε.sum_right {ι : Type*} {ε : ℂ} (hε2 : ε * ε = 1) (g : FormalDist (End ℂ V))
    (s : Finset ι) (f : ι → FormalDist (End ℂ V)) (h : ∀ i ∈ s, Localε ε g (f i)) :
    Localε ε g (∑ i ∈ s, f i) :=
  Localε.symm hε2 (Localε.sum_left ε s f g (fun i hi => Localε.symm hε2 (h i hi)))

/-- A finite `ℂ`-linear combination of generators is `ε`-local with any `g` that is `ε`-local
with every generator.  The `ε` is constant along the combination — this is why parity-homogeneous
combinations behave exactly like the bosonic case. -/
theorem Localε_lc_left {ι : Type*} (ε : ℂ) (fld : ι → FormalDist (End ℂ V)) (c : ι →₀ ℂ)
    (g : FormalDist (End ℂ V)) (h : ∀ i, Localε ε (fld i) g) :
    Localε ε (Finsupp.linearCombination ℂ fld c) g := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Localε.sum_left ε c.support (fun i => c i • fld i) g
    (fun i _ => Localε.smul_left ε (c i) (h i))

/-- Two parity-homogeneous linear combinations of pairwise `ε`-local generators are `ε`-local. -/
theorem Localε_lc_lc {ι : Type*} {ε : ℂ} (hε2 : ε * ε = 1) (fld : ι → FormalDist (End ℂ V))
    (c d : ι →₀ ℂ) (h : ∀ i j, Localε ε (fld i) (fld j)) :
    Localε ε (Finsupp.linearCombination ℂ fld c) (Finsupp.linearCombination ℂ fld d) := by
  rw [show (Finsupp.linearCombination ℂ fld d) = Finsupp.linearCombination ℂ fld d from rfl]
  refine Localε.symm hε2 (Localε_lc_left ε fld d _ (fun j => Localε.symm hε2 ?_))
  exact Localε_lc_left ε fld c (fld j) (fun i => h i j)

/-- Support-restricted form: only the generators actually occurring need be `ε`-local with `g`.
Essential in the super case, where a parity-homogeneous combination is `ε`-local at a single `ε`
only because its support avoids the other parity. -/
theorem Localε_lc_left_support {ι : Type*} (ε : ℂ) (fld : ι → FormalDist (End ℂ V)) (c : ι →₀ ℂ)
    (g : FormalDist (End ℂ V)) (h : ∀ i ∈ c.support, Localε ε (fld i) g) :
    Localε ε (Finsupp.linearCombination ℂ fld c) g := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact Localε.sum_left ε c.support (fun i => c i • fld i) g
    (fun i hi => Localε.smul_left ε (c i) (h i hi))

/-- Two parity-homogeneous combinations, by support. -/
theorem Localε_lc_lc_support {ι : Type*} {ε : ℂ} (hε2 : ε * ε = 1)
    (fld : ι → FormalDist (End ℂ V)) (c d : ι →₀ ℂ)
    (h : ∀ i ∈ c.support, ∀ j ∈ d.support, Localε ε (fld i) (fld j)) :
    Localε ε (Finsupp.linearCombination ℂ fld c) (Finsupp.linearCombination ℂ fld d) := by
  refine Localε.symm hε2 (Localε_lc_left_support ε fld d _ (fun j hj => Localε.symm hε2 ?_))
  exact Localε_lc_left_support ε fld c (fld j) (fun i hi => h i hi j hj)

/-! ## §2  Standalone super Goddard uniqueness -/

/-- **Pointwise standalone super Goddard.**  Identical to `goddard_zero_at`: the hypothesis
`A p vac = 0` is what lets the bracket be rewritten, and it kills the `ε •` term too. -/
theorem goddard_zero_atε (ε : ℂ) (vac b : V) (A Gb : FormalDist (End ℂ V))
    (hloc : Localε ε A Gb) (hcre0 : Gb 0 vac = b) (hcreneg : ∀ q : ℤ, q < 0 → Gb q vac = 0)
    (hAvac : ∀ p : ℤ, A p vac = 0) (m : ℤ) : A m b = 0 := by
  obtain ⟨N, hN⟩ := hloc
  have hDeq : (fun p q : ℤ => A p ((Gb) q vac)) = applyVec vac (bracketDistε ε A Gb) := by
    apply FormalDist₂.ext; intro p q
    show A p ((Gb) q vac) = applyVec vac (bracketDistε ε A Gb) p q
    rw [applyVec_apply, bracketDistε_apply, LinearMap.sub_apply, Module.End.mul_apply,
      LinearMap.smul_apply, Module.End.mul_apply, hAvac, map_zero, smul_zero, sub_zero]
  have hkill : mulBySubPow N (fun p q : ℤ => A p ((Gb) q vac)) = 0 := by
    rw [hDeq, ← applyVec_mulBySubPow, hN, applyVec_zero]
  have hbb : IsBddBelow₂ (fun p q : ℤ => A p ((Gb) q vac)) :=
    ⟨0, fun p q hq => by change A p ((Gb) q vac) = 0; rw [hcreneg q hq, map_zero]⟩
  have hD0 : (fun p q : ℤ => A p ((Gb) q vac)) = 0 :=
    eq_zero_of_mulBySubPow_of_bddBelow N _ hkill hbb
  have hfin := congrFun (congrFun hD0 m) 0
  change A m b = 0
  rw [← hcre0]; exact hfin

/-- **Operator-first super uniqueness.**  A field annihilating the vacuum at every degree and
`ε`-local with a creating test field for each of a spanning family is zero. -/
theorem field_eq_zero_of_vacuumε {ι : Type*} (ε : ι → ℂ) (vac : V) (A : FormalDist (End ℂ V))
    (st : ι → V) (fld : ι → FormalDist (End ℂ V))
    (hloc : ∀ j, Localε (ε j) A (fld j))
    (hcre0 : ∀ j, (fld j) 0 vac = st j)
    (hcreneg : ∀ j, ∀ q : ℤ, q < 0 → (fld j) q vac = 0)
    (hAvac : ∀ p : ℤ, A p vac = 0)
    (hspan : Submodule.span ℂ (Set.range st) = ⊤) :
    A = 0 := by
  funext m
  have hker : Submodule.span ℂ (Set.range st) ≤ LinearMap.ker (A m) := by
    rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact goddard_zero_atε (ε j) vac (st j) A (fld j) (hloc j) (hcre0 j) (hcreneg j) hAvac m
  rw [hspan] at hker
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp hker)

/-! ## §3  The super reconstruction theorem -/

/-- Splitting a `Finsupp` by parity: `c = c|_{par = p} + c|_{par ≠ p}`. -/
theorem finsupp_parity_split {ι : Type*} (par : ι → ZMod 2) (p : ZMod 2) (c : ι →₀ ℂ) :
    c = c.filter (fun i => par i = p) + c.filter (fun i => ¬ (par i = p)) := by
  classical
  apply Finsupp.ext; intro i
  rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  by_cases h : par i = p
  · rw [if_pos h, if_neg (by simpa using h), add_zero]
  · rw [if_neg h, if_pos h, zero_add]

/-- In `ZMod 2`, failing to be `p` means being the other one. -/
theorem zmod_two_ne (p q : ZMod 2) (h : ¬ (q = p)) : q = p + 1 := by revert p q; decide

/-- **The super reconstruction theorem.**  From a parity-graded family of pairwise
`koszul`-local creating fields whose vacuum-creation states span, a linear `YA` with
`YA (st i) = fld i`, satisfying VA3 creation, VA5 regularity, translation covariance, and
`koszul`-locality on parity-homogeneous states.

The extra hypothesis over the bosonic `reconstruct` is `hparity`: a null combination has null
parity components.  It is exactly what `SuperVertexAlgebra.parity_isInternal` supplies, and it is
genuinely needed — Goddard uniqueness applies one `ε` at a time, so `ker S ≤ ker F` has to be
checked parity by parity. -/
theorem reconstructε {ι : Type*} (vac : V) (st : ι → V) (fld : ι → FormalDist (End ℂ V))
    (T : End ℂ V) (par : ι → ZMod 2)
    (hspan : Submodule.span ℂ (Set.range st) = ⊤)
    (hparity : ∀ c : ι →₀ ℂ, Finsupp.linearCombination ℂ st c = 0 → ∀ p : ZMod 2,
        Finsupp.linearCombination ℂ st (c.filter (fun i => par i = p)) = 0)
    (hfield : ∀ i, IsField (fld i))
    (hlocal : ∀ i j, Localε (koszul (par i) (par j)) (fld i) (fld j))
    (hcre0 : ∀ i, (fld i) 0 vac = st i)
    (hcreneg : ∀ i, ∀ q : ℤ, q < 0 → (fld i) q vac = 0)
    (hTvac : T vac = 0)
    (hTcov : ∀ i, DCovariant T (fld i)) :
    ∃ YA : V →ₗ[ℂ] FormalDist (End ℂ V),
      (∀ i, YA (st i) = fld i) ∧
      (∀ u : V, IsField (YA u)) ∧
      (∀ (p q : ZMod 2) (c d : ι →₀ ℂ),
          (∀ i ∈ c.support, par i = p) → (∀ j ∈ d.support, par j = q) →
          Localε (koszul p q) (YA (Finsupp.linearCombination ℂ st c))
            (YA (Finsupp.linearCombination ℂ st d))) ∧
      (∀ u : V, (YA u) 0 vac = u) ∧
      (∀ u : V, ∀ q : ℤ, q < 0 → (YA u) q vac = 0) ∧
      (∀ u : V, DCovariant T (YA u)) := by
  classical
  set S : (ι →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ st with hSdef
  set F : (ι →₀ ℂ) →ₗ[ℂ] FormalDist (End ℂ V) := Finsupp.linearCombination ℂ fld with hFdef
  have hSsurj : Function.Surjective S := by
    rw [← LinearMap.range_eq_top, hSdef, Finsupp.range_linearCombination, hspan]
  -- Vacuum annihilation: unchanged from the bosonic argument (no sign enters).
  have hFvac : ∀ c : (ι →₀ ℂ), S c = 0 → ∀ p : ℤ, (F c) p vac = 0 := by
    intro c hc p
    rcases lt_or_ge p 0 with hp | hp
    · rw [lc_eval, Finsupp.linearCombination_apply, Finsupp.sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hcreneg i p hp, smul_zero]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = (n : ℤ) := ⟨p.toNat, by omega⟩
      clear hp
      have hDcov : DCovariant T (F c) := DCovariant_lc fld c hTcov
      induction n with
      | zero =>
          rw [Nat.cast_zero, lc_eval]
          have hzc : Finsupp.linearCombination ℂ (fun i => (fld i) 0 vac) c = S c := by
            rw [hSdef, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
            exact Finsupp.sum_congr (fun i _ => by rw [hcre0 i])
          rw [hzc, hc]
      | succ n ih =>
          have hrec : T ((F c) (n : ℤ) vac) = ((n : ℤ) + 1) • (F c) ((n : ℤ) + 1) vac := by
            have h := congrArg (fun (R : End ℂ V) => R vac) (hDcov (n : ℤ))
            simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
            rwa [hTvac, map_zero, sub_zero] at h
          have hc' : (((n : ℤ) + 1 : ℤ) : ℂ) ≠ 0 := by rw [Int.cast_ne_zero]; omega
          rw [ih] at hrec
          rw [map_zero] at hrec
          rw [Nat.cast_succ]
          have hz : ((n : ℤ) + 1) • (F c) ((n : ℤ) + 1) vac = 0 := hrec.symm
          rw [← Int.cast_smul_eq_zsmul ℂ ((n : ℤ) + 1)] at hz
          rcases smul_eq_zero.mp hz with h0 | h0
          · exact absurd h0 hc'
          · exact h0
  -- Well-definedness, parity by parity: this is where the super case genuinely differs.
  have hkerHom : ∀ (p : ZMod 2) (c : ι →₀ ℂ), (∀ i ∈ c.support, par i = p) → S c = 0 →
      F c = 0 := by
    intro p c hcp hc
    refine field_eq_zero_of_vacuumε (fun j => koszul p (par j)) vac (F c) st fld
      (fun j => ?_) hcre0 hcreneg (hFvac c hc) hspan
    refine Localε_lc_left_support _ fld c (fld j) (fun i hi => ?_)
    rw [← hcp i hi]
    exact hlocal i j
  have hker : LinearMap.ker S ≤ LinearMap.ker F := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have hsplit := finsupp_parity_split par 0 c
    have h0 : F (c.filter (fun i => par i = 0)) = 0 := by
      refine hkerHom 0 _ (fun i hi => ?_) (hparity c hc 0)
      have := Finsupp.support_filter (p := fun i => par i = 0) (f := c) ▸ hi
      exact (Finset.mem_filter.mp this).2
    have h1 : F (c.filter (fun i => ¬ (par i = 0))) = 0 := by
      have heq : c.filter (fun i => ¬ (par i = 0)) = c.filter (fun i => par i = 1) := by
        apply Finsupp.ext; intro i
        rw [Finsupp.filter_apply, Finsupp.filter_apply]
        by_cases h : par i = 0
        · rw [if_neg (by simpa using h), if_neg (by rw [h]; decide)]
        · rw [if_pos h, if_pos (by simpa using zmod_two_ne 0 (par i) h)]
      rw [heq]
      refine hkerHom 1 _ (fun i hi => ?_) (hparity c hc 1)
      have := Finsupp.support_filter (p := fun i => par i = 1) (f := c) ▸ hi
      exact (Finset.mem_filter.mp this).2
    rw [hsplit, map_add, h0, h1, add_zero]
  -- Build `YA` by factoring `F` through the surjection `S`.
  let YA : V →ₗ[ℂ] FormalDist (End ℂ V) :=
    (Submodule.liftQ (LinearMap.ker S) F hker).comp
      (S.quotKerEquivOfSurjective hSsurj).symm.toLinearMap
  have hYAcomp : ∀ c : (ι →₀ ℂ), YA (S c) = F c := by
    intro c
    show (Submodule.liftQ (LinearMap.ker S) F hker).comp
        (S.quotKerEquivOfSurjective hSsurj).symm.toLinearMap (S c) = F c
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  refine ⟨YA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hst : st i = S (Finsupp.single i 1) := by
      rw [hSdef, Finsupp.linearCombination_single, one_smul]
    rw [hst, hYAcomp, hFdef, Finsupp.linearCombination_single, one_smul]
  · intro u
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp]; exact isField_lc fld c hfield
  · intro p q c d hcp hdq
    rw [show Finsupp.linearCombination ℂ st c = S c from rfl,
      show Finsupp.linearCombination ℂ st d = S d from rfl, hYAcomp, hYAcomp]
    refine Localε_lc_lc_support (koszul_mul_self p q) fld c d (fun i hi j hj => ?_)
    rw [← hcp i hi, ← hdq j hj]
    exact hlocal i j
  · intro u
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp, lc_eval]
    have hzc : Finsupp.linearCombination ℂ (fun i => (fld i) 0 vac) c = S c := by
      rw [hSdef, Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
      exact Finsupp.sum_congr (fun i _ => by rw [hcre0 i])
    rw [hzc]
  · intro u q hq
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp, lc_eval, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hcreneg i q hq, smul_zero]
  · intro u
    obtain ⟨c, rfl⟩ := hSsurj u
    rw [hYAcomp]; exact DCovariant_lc fld c hTcov

end VOA
