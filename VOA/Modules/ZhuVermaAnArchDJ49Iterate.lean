/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUFullWeakU
import VOA.Modules.ZhuVermaAnArchDJ49Star

/-!
# Dong–Jiang Lemma 4.9 — the operator transport `(★) ⟹ ModuleIterate (muFullRhoU W U)`

`ZhuVermaAnArchIterateNonneg` shows that the `ℓ ≥ 0` half of `ModuleIterate` is free, so the entire
content of Dong–Jiang's Lemma 4.9 sits in the regime `ℓ < 0`.  This file performs the **operator
half** of that regime: it reduces `ModuleIterate (muFullRhoU W U)` — for *every* `A(𝒱)`-module `U`
at once — to the single **pure-`𝒱` membership** `(★)`, a statement about `𝒱` alone in which no
module, no tensor product and no graded piece occurs.

## The statement `(★)` (`DJ49Star`, stated in `ZhuVermaAnArchDJ49Star`)

For homogeneous `u ∈ 𝒱_K`, `v ∈ 𝒱_M`, a source level `n : ℕ`, modes `ℓ < 0`, `N : ℤ` and the common
target level `q = K + M − ℓ − N − 2 + n ≥ 0`:

```
  u₍ℓ₎v  −  ∑ᵢ (−1)ⁱ C(ℓ,i) · (u *^q_{n,pᵢ} v)  +  ∑ᵢ (−1)^{ℓ+i} C(ℓ,i) · (v *^q_{n,p'ᵢ} u)
     ∈ O_{q,n}(𝒱)                          (pᵢ = M−N−i−1+n,  p'ᵢ = K−i−1+n)
```

both sums being automatically finite (`pᵢ ≥ 0` forces `i ≤ M−N−1+n`; `p'ᵢ ≥ 0` forces `i ≤ K−1+n`,
and `C(ℓ,i) = 0` for `i < 0`).  Levels are carried as *integers* through `anmGenZ`, which is
`anmGen` at a nonnegative level and `0` at a negative one — exactly matching the fact that a mode
composition through a negative graded piece of `M(U)` is zero.

## Why the reduction works

On `M(U)` **every composition of two modes collapses to a single mode**, by the unconditional
`oFullU_comp` (DJ Lemma 4.1):

* `v₍N₊ᵢ₎ : M(U)(n) → M(U)(pᵢ)` and then `u₍ℓ₋ᵢ₎ : M(U)(pᵢ) → M(U)(q)`, composing to
  `o_{q,n}(u *^q_{n,pᵢ} v)`;
* `u₍ᵢ₎ : M(U)(n) → M(U)(p'ᵢ)` and then `v₍ℓ₊N₋ᵢ₎ : M(U)(p'ᵢ) → M(U)(q)`, composing to
  `o_{q,n}(v *^q_{n,p'ᵢ} u)`;
* `(u₍ℓ₎v)₍N₎ : M(U)(n) → M(U)(q)` is `o_{q,n}(u₍ℓ₎v)`.

Every term therefore lands in the *same* level `q`, and the whole identity is the image of one
representative-level identity under the linear map `D ↦ o_{q,n}(D)x`, which kills `O_{q,n}(𝒱)` by
`anmGen_OnmFull_right_unconditional` (DJ Lemma 2.8, right inclusion).  The four level regimes
(`q < 0`; `q ≥ 0` with either intermediate level negative) are handled exactly as in
`muFullMode_commutator_incl`.

## What is proved here

* `oFullU_eq_zero_of_mem` — `o_{n,m}(D) = 0` for `D ∈ O_{n,m}(𝒱)` (the descent engine);
* `oFullUAt` — the bundled linear map `D ↦ o_{q,n}(D)x : 𝒱 →ₗ M(U)`;
* `itRHS` and its finiteness/bilinearity API for an arbitrary `V̂`-representation;
* `muFullMode_iterate_incl` — the four-regime core, on one graded piece;
* **`moduleIterate_of_dj49Star`** — `DJ49Star W → ModuleIterate (muFullRhoU W U)`, combining the
  `ℓ < 0` transport with the free `ℓ ≥ 0` half (`moduleIterate_nonneg`);
* `muFullWeakOfStar` / `muFullLWModuleOfStar` — the resulting `WeakModule`/`LWModule` packaging.

**`DJ49Star W` is NOT proved here.**  It is carried as an explicit hypothesis (never an axiom, never
a `sorry`); its scalar core is the proved `dj49_master` (`ZhuVermaAnArchDJ49Master`).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`), pbw-free.

## References
Dong–Jiang math/0601626 §4 (Lemmas 4.1, 4.8, 4.9 and the Corollary after 4.9), §2 (Lemma 2.8);
`ZhuVermaAnArchMUFullActionU` (`oFullU`, `oFullU_comp`), `ZhuVermaAnArchMUFullMode`
(`muFullMode`, `oLevelIncl`, `muFull_end_ext`), `ZhuVermaAnArchDJ28Final`
(`anmGen_OnmFull_right_unconditional`), `ZhuVermaAnArchMUjacobi` (`ModuleIterate`),
`ZhuVermaAnArchIterateNonneg` (`moduleIterate_nonneg`).
-/

namespace VOA

open VertexOperatorAlgebra
open VHat VHat.VHatRep
open scoped TensorProduct DirectSum BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The descent engine: `o_{n,m}` kills the ideal -/

/-- **The `M(U)` mode operator of an ideal element vanishes.**  If `D ∈ O_{n,m}(𝒱)` then
`o_{n,m}(D) = 0` on `M(U)(m)`.  This is DJ Lemma 2.8's right inclusion
(`anmGen_OnmFull_right_unconditional`) read as a statement about operators. -/
theorem oFullU_eq_zero_of_mem (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ) {D : 𝒱}
    (hD : D ∈ OnmFull W n m) : oFullU W U n m D = 0 := by
  apply TensorProduct.ext'
  intro y w
  obtain ⟨g, rfl⟩ := (OnmFull W m 0).mkQ_surjective y
  show oFullU W U n m D (mkAnmFull W m 0 g ⊗ₜ[ℂ] w) = 0
  rw [oFullU_tmul,
    show mkAnmFull W n 0 (anmGen W n 0 m D g) = 0 from by
      rw [mkAnmFull, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact anmGen_OnmFull_right_unconditional W n 0 m g D hD]
  exact TensorProduct.zero_tmul _ _

/-- **The evaluation map `D ↦ o_{n,m}(D)x`, bundled.**  Linear in the acting vector `D`, so it
commutes with finite sums and kills `O_{n,m}(𝒱)`; this is the single map through which the whole
representative-level identity `(★)` is pushed to `M(U)`. -/
noncomputable def oFullUAt (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ)
    (x : MUPieceFull W U m) : 𝒱 →ₗ[ℂ] MUFull W U where
  toFun D := MUFull.incl W U n (oFullU W U n m D x)
  map_add' D₁ D₂ := by
    simp only [oFullU_add_acting W U n m D₁ D₂, LinearMap.add_apply, map_add]
  map_smul' c D := by
    simp only [oFullU_smul_acting W U n m c D, LinearMap.smul_apply, map_smul, RingHom.id_apply]

@[simp] theorem oFullUAt_apply (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ)
    (x : MUPieceFull W U m) (D : 𝒱) :
    oFullUAt W U n m x D = MUFull.incl W U n (oFullU W U n m D x) := rfl

/-- The evaluation map kills the ideal. -/
theorem oFullUAt_eq_zero_of_mem (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (n m : ℕ)
    (x : MUPieceFull W U m) {D : 𝒱} (hD : D ∈ OnmFull W n m) : oFullUAt W U n m x D = 0 := by
  rw [oFullUAt_apply, oFullU_eq_zero_of_mem W U n m hD]
  simp

/-! ## §2  The right-hand side of `ModuleIterate`, as a named family -/

section ItRHS

variable {Mo : Type u} [AddCommGroup Mo] [Module ℂ Mo] {W : VertexOperatorAlgebra 𝒱}

/-- **The right-hand side of `ModuleIterate`.**  Naming it makes the (tri)linearity bookkeeping of
the reduction to homogeneous vectors and to a single graded piece available as lemmas. -/
noncomputable def itRHS (ρ : VHatRep W Mo) (u v : 𝒱) (x : Mo) (ℓ N : ℤ) : Mo :=
  ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
    (ρ.actMode u (ℓ - i) (ρ.actMode v (N + i) x)
      - negOnePow ℓ • ρ.actMode v (ℓ + N - i) (ρ.actMode u i x))

/-- `ModuleIterate` restated with the named right-hand side. -/
theorem moduleIterate_iff_itRHS (ρ : VHatRep W Mo) :
    ModuleIterate ρ ↔
      ∀ (u v : 𝒱) (x : Mo) (ℓ N : ℤ), ρ.actMode (W.smul u ℓ v) N x = itRHS ρ u v x ℓ N :=
  Iff.rfl

/-- The summand family of `itRHS` is finitely supported: `C(ℓ,i)` kills `i < 0` and the truncation
property kills large `i`. -/
theorem itRHS_fin (ρ : VHatRep W Mo) (htr : ActModeTruncated ρ) (u v : 𝒱) (x : Mo) (ℓ N : ℤ) :
    (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
      (ρ.actMode u (ℓ - i) (ρ.actMode v (N + i) x)
        - negOnePow ℓ • ρ.actMode v (ℓ + N - i) (ρ.actMode u i x))).Finite := by
  obtain ⟨Nv, hNv⟩ := htr v x
  obtain ⟨Nu, hNu⟩ := htr u x
  set B : ℤ := max (Nv - N) Nu with hB
  have hB₁ : Nv - N ≤ B := le_max_left _ _
  have hB₂ : Nu ≤ B := le_max_right _ _
  refine Set.Finite.subset (Set.finite_Icc 0 B) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · rw [hNv (N + i) (by omega), hNu i (by omega)]
    simp

theorem itRHS_zero_x (ρ : VHatRep W Mo) (u v : 𝒱) (ℓ N : ℤ) : itRHS ρ u v (0 : Mo) ℓ N = 0 := by
  rw [itRHS]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by simp

theorem itRHS_zero_u (ρ : VHatRep W Mo) (v : 𝒱) (x : Mo) (ℓ N : ℤ) :
    itRHS ρ (0 : 𝒱) v x ℓ N = 0 := by
  rw [itRHS]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by simp

theorem itRHS_zero_v (ρ : VHatRep W Mo) (u : 𝒱) (x : Mo) (ℓ N : ℤ) :
    itRHS ρ u (0 : 𝒱) x ℓ N = 0 := by
  rw [itRHS]
  exact finsum_eq_zero_of_forall_eq_zero fun i => by simp

theorem itRHS_add_x (ρ : VHatRep W Mo) (htr : ActModeTruncated ρ) (u v : 𝒱) (x y : Mo) (ℓ N : ℤ) :
    itRHS ρ u v (x + y) ℓ N = itRHS ρ u v x ℓ N + itRHS ρ u v y ℓ N := by
  rw [itRHS, itRHS, itRHS,
    ← finsum_add_distrib (itRHS_fin ρ htr u v x ℓ N) (itRHS_fin ρ htr u v y ℓ N)]
  refine finsum_congr fun i => ?_
  simp only [map_add]
  module

theorem itRHS_add_u (ρ : VHatRep W Mo) (htr : ActModeTruncated ρ) (u₁ u₂ v : 𝒱) (x : Mo)
    (ℓ N : ℤ) :
    itRHS ρ (u₁ + u₂) v x ℓ N = itRHS ρ u₁ v x ℓ N + itRHS ρ u₂ v x ℓ N := by
  rw [itRHS, itRHS, itRHS,
    ← finsum_add_distrib (itRHS_fin ρ htr u₁ v x ℓ N) (itRHS_fin ρ htr u₂ v x ℓ N)]
  refine finsum_congr fun i => ?_
  simp only [actMode_add_left, LinearMap.add_apply, map_add]
  module

theorem itRHS_add_v (ρ : VHatRep W Mo) (htr : ActModeTruncated ρ) (u v₁ v₂ : 𝒱) (x : Mo)
    (ℓ N : ℤ) :
    itRHS ρ u (v₁ + v₂) x ℓ N = itRHS ρ u v₁ x ℓ N + itRHS ρ u v₂ x ℓ N := by
  rw [itRHS, itRHS, itRHS,
    ← finsum_add_distrib (itRHS_fin ρ htr u v₁ x ℓ N) (itRHS_fin ρ htr u v₂ x ℓ N)]
  refine finsum_congr fun i => ?_
  simp only [actMode_add_left, LinearMap.add_apply, map_add]
  module

end ItRHS

/-! ## §3  The bridge `actMode ↔ muFullMode` at the unconditional representation -/

/-- The `𝒱`-modes of `muFullRhoU` are the `M(U)` modes `muFullMode`. -/
theorem muFullRhoU_actMode (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (a : 𝒱) (m : ℤ) :
    (muFullRhoU W U).actMode a m = muFullMode W U m a :=
  muFullRho_actMode W U (mUFullBracket_holds W U) a m

/-! ## §4  The four-regime core, on one graded piece -/

/-- **The `ℓ < 0` iterate identity on a single graded piece of `M(U)`, given `(★)`.**

All four level regimes of `muFullMode_commutator_incl` recur here: the common target level
`q = K + M − ℓ − N − 2 + n` is negative (everything vanishes), or nonnegative with either
intermediate level `pᵢ = M − N − i − 1 + n`, `p'ᵢ = K − i − 1 + n` negative (that term vanishes) or
nonnegative (the two modes compose to a single mode by `oFullU_comp`). -/
theorem muFullMode_iterate_incl (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (hstar : DJ49Star W)
    {K M : ℕ} {u v : 𝒱} (hu : u ∈ W.grading (K : ℤ)) (hv : v ∈ W.grading (M : ℤ))
    {ℓ : ℤ} (hℓ : ℓ < 0) (N : ℤ) (n : ℕ) (x : MUPieceFull W U n) :
    muFullMode W U N (W.smul u ℓ v) (MUFull.incl W U n x)
      = ∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (muFullMode W U (ℓ - i) u (muFullMode W U (N + i) v (MUFull.incl W U n x))
            - negOnePow ℓ • muFullMode W U (ℓ + N - i) v
                (muFullMode W U i u (MUFull.incl W U n x))) := by
  have huv : W.smul u ℓ v ∈ W.grading ((K : ℤ) + (M : ℤ) - ℓ - 1) := smul_mem_grading W hu hv ℓ
  -- evaluation of a single mode application of `u`, in the two regimes
  have hEu : ∀ (s t : ℕ) (p : ℤ) (y : MUPieceFull W U s), (K : ℤ) - p - 1 + (s : ℤ) = (t : ℤ) →
      muFullMode W U p u (MUFull.incl W U s y) = MUFull.incl W U t (oFullU W U t s u y) := by
    intro s t p y h
    rw [muFullMode_apply_incl W U p hu s y,
      oLevelIncl_eq_of_target W U (show muTargetLevel (K : ℤ) p s = (t : ℤ) from h) u,
      LinearMap.comp_apply]
  have hZu : ∀ (s : ℕ) (p : ℤ) (y : MUPieceFull W U s), (K : ℤ) - p - 1 + (s : ℤ) < 0 →
      muFullMode W U p u (MUFull.incl W U s y) = 0 := by
    intro s p y h
    rw [muFullMode_apply_incl W U p hu s y,
      oLevelIncl_of_neg W U (show muTargetLevel (K : ℤ) p s < 0 from h) u, LinearMap.zero_apply]
  have hEv : ∀ (s t : ℕ) (p : ℤ) (y : MUPieceFull W U s), (M : ℤ) - p - 1 + (s : ℤ) = (t : ℤ) →
      muFullMode W U p v (MUFull.incl W U s y) = MUFull.incl W U t (oFullU W U t s v y) := by
    intro s t p y h
    rw [muFullMode_apply_incl W U p hv s y,
      oLevelIncl_eq_of_target W U (show muTargetLevel (M : ℤ) p s = (t : ℤ) from h) v,
      LinearMap.comp_apply]
  have hZv : ∀ (s : ℕ) (p : ℤ) (y : MUPieceFull W U s), (M : ℤ) - p - 1 + (s : ℤ) < 0 →
      muFullMode W U p v (MUFull.incl W U s y) = 0 := by
    intro s p y h
    rw [muFullMode_apply_incl W U p hv s y,
      oLevelIncl_of_neg W U (show muTargetLevel (M : ℤ) p s < 0 from h) v, LinearMap.zero_apply]
  by_cases hT : 0 ≤ (K : ℤ) + (M : ℤ) - ℓ - N - 2 + (n : ℤ)
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, (K : ℤ) + (M : ℤ) - ℓ - N - 2 + (n : ℤ) = (q : ℤ) :=
      ⟨_, (Int.toNat_of_nonneg hT).symm⟩
    -- the left-hand side, through the evaluation map
    have hL : muFullMode W U N (W.smul u ℓ v) (MUFull.incl W U n x)
        = oFullUAt W U q n x (W.smul u ℓ v) := by
      rw [muFullMode_apply_incl W U N huv n x,
        oLevelIncl_eq_of_target W U
          (show muTargetLevel ((K : ℤ) + (M : ℤ) - ℓ - 1) N n = (q : ℤ) from by
            simp only [muTargetLevel]; omega) (W.smul u ℓ v)]
      rfl
    -- the `u₍ℓ₋ᵢ₎v₍N₊ᵢ₎` family
    have hA : ∀ i : ℤ,
        muFullMode W U (ℓ - i) u (muFullMode W U (N + i) v (MUFull.incl W U n x))
          = oFullUAt W U q n x (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v) := by
      intro i
      by_cases hp : 0 ≤ (M : ℤ) - N - i - 1 + (n : ℤ)
      · obtain ⟨P, hP⟩ : ∃ P : ℕ, (M : ℤ) - N - i - 1 + (n : ℤ) = (P : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        have hcomp := congrArg (fun f : MUPieceFull W U n →ₗ[ℂ] MUPieceFull W U q => f x)
          (oFullU_comp W U q n P u v)
        simp only [LinearMap.comp_apply] at hcomp
        rw [hEv n P (N + i) x (by omega), hEu P q (ℓ - i) (oFullU W U P n v x) (by omega), hcomp,
          anmGenZ_of_eq W q n hP u v]
        rfl
      · rw [hZv n (N + i) x (by omega), map_zero, anmGenZ_of_neg W q n (by omega), map_zero]
    -- the `v₍ℓ₊N₋ᵢ₎u₍ᵢ₎` family
    have hBm : ∀ i : ℤ,
        muFullMode W U (ℓ + N - i) v (muFullMode W U i u (MUFull.incl W U n x))
          = oFullUAt W U q n x (anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u) := by
      intro i
      by_cases hp : 0 ≤ (K : ℤ) - i - 1 + (n : ℤ)
      · obtain ⟨P, hP⟩ : ∃ P : ℕ, (K : ℤ) - i - 1 + (n : ℤ) = (P : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        have hcomp := congrArg (fun f : MUPieceFull W U n →ₗ[ℂ] MUPieceFull W U q => f x)
          (oFullU_comp W U q n P v u)
        simp only [LinearMap.comp_apply] at hcomp
        rw [hEu n P i x (by omega), hEv P q (ℓ + N - i) (oFullU W U P n u x) (by omega), hcomp,
          anmGenZ_of_eq W q n hP v u]
        rfl
      · rw [hZu n i x (by omega), map_zero, anmGenZ_of_neg W q n (by omega), map_zero]
    -- the representative-level family is finitely supported
    have hfin : (Function.support fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
          - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u)).Finite := by
      set B : ℤ := max ((M : ℤ) - N - 1 + (n : ℤ)) ((K : ℤ) - 1 + (n : ℤ)) with hBdef
      have hB₁ : (M : ℤ) - N - 1 + (n : ℤ) ≤ B := le_max_left _ _
      have hB₂ : (K : ℤ) - 1 + (n : ℤ) ≤ B := le_max_right _ _
      refine Set.Finite.subset (Set.finite_Icc 0 B) ?_
      intro i hi
      rw [Function.mem_support] at hi
      rw [Set.mem_Icc]
      refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
      · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
      · rw [anmGenZ_of_neg W q n (show (M : ℤ) - N - i - 1 + (n : ℤ) < 0 from by omega),
          anmGenZ_of_neg W q n (show (K : ℤ) - i - 1 + (n : ℤ) < 0 from by omega)]
        simp
    -- push the whole right-hand side through the evaluation map
    have hRHS : (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
          (muFullMode W U (ℓ - i) u (muFullMode W U (N + i) v (MUFull.incl W U n x))
            - negOnePow ℓ • muFullMode W U (ℓ + N - i) v
                (muFullMode W U i u (MUFull.incl W U n x))))
        = oFullUAt W U q n x (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
            (anmGenZ W q n ((M : ℤ) - N - i - 1 + (n : ℤ)) u v
              - negOnePow ℓ • anmGenZ W q n ((K : ℤ) - i - 1 + (n : ℤ)) v u)) := by
      rw [map_finsum (oFullUAt W U q n x) hfin]
      refine finsum_congr fun i => ?_
      rw [hA i, hBm i, map_smul, map_sub, map_smul]
    have hz := oFullUAt_eq_zero_of_mem W U q n x (hstar K M u v hu hv n q ℓ N hℓ hq.symm)
    rw [map_sub] at hz
    rw [hL, hRHS, ← sub_eq_zero]
    exact hz
  · -- the common target level is negative: every term vanishes
    rw [not_le] at hT
    have hL : muFullMode W U N (W.smul u ℓ v) (MUFull.incl W U n x) = 0 := by
      rw [muFullMode_apply_incl W U N huv n x,
        oLevelIncl_of_neg W U
          (show muTargetLevel ((K : ℤ) + (M : ℤ) - ℓ - 1) N n < 0 from by
            simp only [muTargetLevel]; omega) (W.smul u ℓ v)]
      rfl
    rw [hL]
    refine (finsum_eq_zero_of_forall_eq_zero fun i => ?_).symm
    have h1 : muFullMode W U (ℓ - i) u (muFullMode W U (N + i) v (MUFull.incl W U n x)) = 0 := by
      by_cases hp : 0 ≤ (M : ℤ) - N - i - 1 + (n : ℤ)
      · obtain ⟨P, hP⟩ : ∃ P : ℕ, (M : ℤ) - N - i - 1 + (n : ℤ) = (P : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        rw [hEv n P (N + i) x (by omega), hZu P (ℓ - i) (oFullU W U P n v x) (by omega)]
      · rw [hZv n (N + i) x (by omega), map_zero]
    have h2 : muFullMode W U (ℓ + N - i) v (muFullMode W U i u (MUFull.incl W U n x)) = 0 := by
      by_cases hp : 0 ≤ (K : ℤ) - i - 1 + (n : ℤ)
      · obtain ⟨P, hP⟩ : ∃ P : ℕ, (K : ℤ) - i - 1 + (n : ℤ) = (P : ℤ) :=
          ⟨_, (Int.toNat_of_nonneg hp).symm⟩
        rw [hEu n P i x (by omega), hZv P (ℓ + N - i) (oFullU W U P n u x) (by omega)]
      · rw [hZu n i x (by omega), map_zero]
    rw [h1, h2]
    simp

/-! ## §5  The `ℓ < 0` regime, for arbitrary vectors -/

/-- The `ℓ < 0` iterate identity for arbitrary `u`, `v` and arbitrary `x : M(U)`, given `(★)`. -/
theorem iterate_neg_of_dj49Star (W : VertexOperatorAlgebra 𝒱) (U : AMod W) (hstar : DJ49Star W)
    {ℓ : ℤ} (hℓ : ℓ < 0) (N : ℤ) :
    ∀ (u v : 𝒱) (x : MUFull W U),
      (muFullRhoU W U).actMode (W.smul u ℓ v) N x = itRHS (muFullRhoU W U) u v x ℓ N := by
  have htr : ActModeTruncated (muFullRhoU W U) := muFullActModeTruncatedU W U
  have hact : ∀ (a : 𝒱) (m : ℤ), (muFullRhoU W U).actMode a m = muFullMode W U m a :=
    muFullRhoU_actMode W U
  refine reduce_homogeneous W (P := fun u => ∀ (v : 𝒱) (x : MUFull W U),
    (muFullRhoU W U).actMode (W.smul u ℓ v) N x = itRHS (muFullRhoU W U) u v x ℓ N) ?_ ?_ ?_
  · intro Ku a ha
    refine reduce_homogeneous W (P := fun v => ∀ x : MUFull W U,
      (muFullRhoU W U).actMode (W.smul a ℓ v) N x = itRHS (muFullRhoU W U) a v x ℓ N) ?_ ?_ ?_
    · intro Mb b hb
      rcases lt_or_ge Ku 0 with hKneg | hKpos
      · have ha0 : a = 0 := by
          have h := W.positivity Ku hKneg
          rw [h, Submodule.mem_bot] at ha; exact ha
        subst ha0
        intro x
        rw [PreVertexAlgebra.smul_zero_left, actMode_zero_left, LinearMap.zero_apply,
          itRHS_zero_u]
      rcases lt_or_ge Mb 0 with hMneg | hMpos
      · have hb0 : b = 0 := by
          have h := W.positivity Mb hMneg
          rw [h, Submodule.mem_bot] at hb; exact hb
        subst hb0
        intro x
        rw [PreVertexAlgebra.smul_zero_right, actMode_zero_left, LinearMap.zero_apply,
          itRHS_zero_v]
      obtain ⟨K, rfl⟩ := Int.eq_ofNat_of_zero_le hKpos
      obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hMpos
      intro x
      refine DirectSum.induction_on x ?_ ?_ ?_
      · rw [map_zero, itRHS_zero_x]
      · intro n y
        show (muFullRhoU W U).actMode (W.smul a ℓ b) N (MUFull.incl W U n y) = _
        rw [hact, itRHS]
        simp only [hact]
        exact muFullMode_iterate_incl W U hstar ha hb hℓ N n y
      · intro x₁ x₂ h₁ h₂
        rw [map_add, h₁, h₂, itRHS_add_x (muFullRhoU W U) htr]
    · intro x
      rw [PreVertexAlgebra.smul_zero_right, actMode_zero_left, LinearMap.zero_apply, itRHS_zero_v]
    · intro v₁ v₂ h₁ h₂ x
      rw [PreVertexAlgebra.smul_add_right, actMode_add_left, LinearMap.add_apply, h₁ x, h₂ x,
        itRHS_add_v (muFullRhoU W U) htr]
  · intro v x
    rw [PreVertexAlgebra.smul_zero_left, actMode_zero_left, LinearMap.zero_apply, itRHS_zero_u]
  · intro u₁ u₂ h₁ h₂ v x
    rw [PreVertexAlgebra.smul_add_left, actMode_add_left, LinearMap.add_apply, h₁ v x, h₂ v x,
      itRHS_add_u (muFullRhoU W U) htr]

/-! ## §6  `ModuleIterate` from `(★)` -/

/-- **`ModuleIterate (muFullRhoU W U)` from the pure-`𝒱` statement `(★)`.**

The `ℓ ≥ 0` half is free (`moduleIterate_nonneg`); the `ℓ < 0` half — Dong–Jiang Lemma 4.9 — is
transported from `(★)` by `iterate_neg_of_dj49Star`.  Note that the hypothesis `DJ49Star W`
mentions neither `U` nor `M(U)`: one pure-`𝒱` statement serves every `A(𝒱)`-module at once. -/
theorem moduleIterate_of_dj49Star (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hstar : DJ49Star W) : ModuleIterate (muFullRhoU W U) := by
  intro u v x ℓ N
  rcases lt_or_ge ℓ 0 with hneg | hpos
  · exact iterate_neg_of_dj49Star W U hstar hneg N u v x
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    exact moduleIterate_nonneg (muFullRhoU W U) (muFullActModeTruncatedU W U) u v x j N

/-- **`M(U)` is a weak `𝒱`-module, given `(★)`.**  Every other input of Dong–Jiang Theorem 4.10 is
already discharged unconditionally. -/
noncomputable def muFullWeakOfStar (W : VertexOperatorAlgebra 𝒱) (U : AMod W)
    (hstar : DJ49Star W) : WeakModule W (MUFull W U) :=
  muFullWeakU W U (moduleIterate_of_dj49Star W U hstar)

/-- **DJ's `M(U)` as a bundled lowest-weight `𝒱`-module, given `(★)`** and the three standard
graded-packaging fields. -/
noncomputable def muFullLWModuleOfStar (W : VertexOperatorAlgebra 𝒱) (U : AMod W) {h : ℂ}
    (hstar : DJ49Star W)
    (hL0 : ∀ (n : ℕ) (x : MUFull W U), x ∈ MUFull.deg W U n →
      muFullMode W U 1 W.conformalVector x = ((h : ℂ) + n) • x)
    (hfin : ∀ n : ℕ, FiniteDimensional ℂ (MUFull.deg W U n))
    (hbot : MUFull.deg W U 0 ≠ ⊥) :
    LWModule W :=
  muFullLWModuleU (moduleIterate_of_dj49Star W U hstar) hL0 hfin hbot

end VOA

/-
`#print axioms` check (each of the following prints `[propext, Classical.choice, Quot.sound]`,
NO `pbw`, NO `sorryAx`):

  #print axioms VOA.oFullU_eq_zero_of_mem
  #print axioms VOA.oFullUAt
  #print axioms VOA.itRHS_fin
  #print axioms VOA.muFullRhoU_actMode
  #print axioms VOA.muFullMode_iterate_incl
  #print axioms VOA.iterate_neg_of_dj49Star
  #print axioms VOA.moduleIterate_of_dj49Star
  #print axioms VOA.muFullWeakOfStar
  #print axioms VOA.muFullLWModuleOfStar
-/
