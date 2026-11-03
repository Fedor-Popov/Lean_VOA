/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modularity.SquareBracketWitt

/-!
# The torus-Virasoro relation for the square-bracket modes  (Gannon 5.3.16, Zhu §4)

The bracket identity `sqBracketCoeff_witt_identity` (`SquareBracketWitt`) is the *scalar* content of
the torus-Virasoro relation `[Lsq m, Lsq n] = (m−n) Lsq (m+n) + (central)`.  To turn it into an operator
statement one first rewrites the commutator `⁅Lsq m, Lsq n⁆` as a **double sum over the ordinary
Virasoro commutators** `⁅W.L a, W.L b⁆` — this file — and then feeds `L_virasoro` in.

The `ω`-part of `Lsq` is `Lω m := vSqZ ω 2 (m+1)`, which acts as `Σ_a d[m,a] • L_a` (`vSqZ_omega_apply`),
reindexing the mode sum `i = a+1` (`mode (Y ω) i = L_{i−1}`, `L_def`).

## Status
The square-bracket Virasoro relation is proved (`Lsq_virasoro_apply`), axiom-clean
`[propext, Classical.choice, Quot.sound]` and `pbw`-**free**:
`⁅L[m], L[n]⁆ = (m−n)·L[m+n] + δ_{m+n,0}·((m³−m)/12)·c` — the same central charge `c` (Gannon 5.3.15).
Its sole input is the named hypothesis `CentralMomentClosed` (the Gel'fand–Fuks closed form of
`centralMoment`; honest `Prop` data, **not** an axiom), whose `m+n ≥ 0` cases are proved here
(`centralMoment_of_pos`, `centralMoment_of_zero`) and whose `m+n < 0` cases are the remaining deep
content.  The vacuum scalars are fully proved: `s(k) = δ_{k,−1}`
(`sqBracketCoeffZ_vacuum_of_ne`/`_neg_one`, in `SquareBracketWitt`) — this is exactly what cancels the
`m+n = −2` Schwarzian anomaly.

Supporting layer (all axiom-clean, `pbw`-free):
* `finsum_sub_distrib`, `finsum_finsum_comm` — general finsum subtraction and the **`ℤ×ℤ` swap** (via
  `finsum_curry` + `finsum_comp_equiv (Equiv.prodComm)`);
* `vSqZ_omega_apply` — `Lω m x = Σ_a d[m,a] • L_a x` (mode reindex `i = a+1`);
* `dL_support_finite`, `dLcomp_support_finite`, `dLmul_support_finite`, `jointSupport_finite` — the
  finite-support lemmas, incl. the **joint rectangle** (a finite biUnion over the `dL(n,x)`-support with
  per-`b` fibres `dL(m, L_b x)` — the union-not-rectangle crux **resolved**);
* `vSqZ_omega_comp` — `Lω m (Lω n x) = Σ_b Σ_a (d[m,a]·d[n,b]) • L_a (L_b x)`;
* `vSqZ_omega_commutator` — `⁅Lω m, Lω n⁆ x = Σ_b Σ_a (d[m,a]d[n,b] − d[n,a]d[m,b]) • L_a(L_b x)` (the
  commutator as a single double sum);
* `vSqZ_vacuum_scalar` — `𝟙[k] = c(0,k,−1) • id` (engine: `c(0,−1,−1)=1`, all other `k` give `0`).

* `vSqZ_omega_lie` (**Form B**) — `⁅Lω m, Lω n⁆ x = Σ_a Σ_b d[m,a]d[n,b] • ⁅L a, L b⁆ x`;
* `bracketDouble_collapse` — `Σ_a Σ_b d[m,a]d[n,b]·(a−b) • L_{a+b} x = (m−n) • Lω(m+n) x`, where
  `sqBracketCoeff_witt_identity` (B(i)) does its job after the `b ↦ j = a+b` reindex;
* `vSqZ_omega_virasoro` — `⁅Lω m, Lω n⁆ x = (m−n)•Lω(m+n)x + ((c/12)·S(m,n))•x`;
* `Lsq_commutator_eq_omega` — the `𝟙`-terms are scalars, so they cancel from the **commutator**
  (but are kept on the right-hand side, where they cancel the anomaly).

**The one remaining open item of GOAL B:** `CentralMomentClosed` for `m+n < 0` — the Gel'fand–Fuks
cocycle.  Engine-verified in exact rationals (0 mismatches over all 1369 pairs `m,n ∈ [−18,18]`), with
the closed form `S(m,n) = Res_w(f_m‴·f_n)`, `f_m = (1+w)(log(1+w))^{m+1}` (constant exactly `1`; ⚠ the
residue must be taken of `f`, **not** of `P` — `Res(P‴·P) ≡ 0` — and the cubic weight lives on the
`m`-slot, else the cocycle flips sign).  Equivalent antidiagonal form:
`S(m,n) = Σ_{p+q=J} [wᵖ]P_m·[w^q]P_n·((m+p)³−(m+p))` with `J = −m−n`, which reduces to a **polynomial
identity in `m` for each `J ≥ 1`** (`J = 2` gives `−(m+1) = −(m−n)/2`; every other `J ≥ 1` gives `0`).
-/

namespace VOA

open PowerSeries
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-- **`∑ᶠ (f − g) = ∑ᶠ f − ∑ᶠ g`** for finitely-supported `f, g` (not in Mathlib's `Finprod`; built from
`finsum_add_distrib` + `finsum_neg_distrib`). -/
theorem finsum_sub_distrib {ι M : Type*} [AddCommGroup M] {f g : ι → M}
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite) :
    ∑ᶠ i, (f i - g i) = ∑ᶠ i, f i - ∑ᶠ i, g i := by
  have hng : (Function.support fun i => -g i).Finite := by
    show (Function.support (-g)).Finite
    rw [Function.support_neg]; exact hg
  rw [sub_eq_add_neg, ← finsum_neg_distrib, ← finsum_add_distrib hf hng]
  exact finsum_congr (fun i => by rw [sub_eq_add_neg])

/-- **Swap of two `ℤ`-indexed finsums** for a jointly finitely-supported family (Mathlib has only the
`a`-then-`b` `finsum_curry` and the *bounded* `finsum_mem_comm`): via `finsum_curry` both ways +
`finsum_comp_equiv (Equiv.prodComm)`. -/
theorem finsum_finsum_comm {M : Type*} [AddCommMonoid M] (F : ℤ → ℤ → M)
    (hF : (Function.support fun p : ℤ × ℤ => F p.1 p.2).Finite) :
    ∑ᶠ b : ℤ, ∑ᶠ a : ℤ, F a b = ∑ᶠ a : ℤ, ∑ᶠ b : ℤ, F a b := by
  have hswap : (Function.support fun q : ℤ × ℤ => F q.2 q.1).Finite := by
    have hpre : (Function.support fun q : ℤ × ℤ => F q.2 q.1)
        = (Equiv.prodComm ℤ ℤ) ⁻¹' (Function.support fun p : ℤ × ℤ => F p.1 p.2) := rfl
    rw [hpre]
    exact hF.preimage ((Equiv.prodComm ℤ ℤ).injective.injOn)
  calc ∑ᶠ b : ℤ, ∑ᶠ a : ℤ, F a b
      = ∑ᶠ q : ℤ × ℤ, F q.2 q.1 := (finsum_curry (fun q : ℤ × ℤ => F q.2 q.1) hswap).symm
    _ = ∑ᶠ p : ℤ × ℤ, F p.1 p.2 :=
        finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := fun p : ℤ × ℤ => F p.1 p.2)
    _ = ∑ᶠ a : ℤ, ∑ᶠ b : ℤ, F a b := finsum_curry (fun p : ℤ × ℤ => F p.1 p.2) hF

/-- **`Lω m` acts as `Σ_a d[m,a] • L_a`.**  The `ω`-part `vSqZ ω 2 (m+1)` of `Lsq m`, with the mode sum
reindexed `i = a+1` and `mode (Y ω) i = L_{i−1}` (`VertexOperatorAlgebra.L_def`). -/
theorem vSqZ_omega_apply (W : VertexOperatorAlgebra 𝒱) (m : ℤ) (x : 𝒱) :
    vSqZ W W.conformalVector 2 (m + 1) x
      = ∑ᶠ a : ℤ, sqBracketCoeffZ 2 (m + 1) (a + 1) • W.L a x := by
  rw [vSqZ_apply]
  refine finsum_eq_of_bijective (fun i => i - 1)
    ⟨fun a b h => by simpa using h, fun b => ⟨b + 1, by ring⟩⟩ (fun i => ?_)
  rw [show ((i - 1) + 1) = i from by ring]
  congr 1
  rw [VertexOperatorAlgebra.L_def, show ((i - 1) + 1) = i from by ring]

/-- **Finite support of `b ↦ d[n,b] • L_b x`** — the `ω`-part summand, reindexed from
`sqModeZ_support_finite` (`b ↦ b+1`, `L_b x = mode (Y ω)(b+1) x`).  Needed to push the linear map `Lω m`
through the finsum (`map_finsum`). -/
theorem dL_support_finite (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (x : 𝒱) :
    (Function.support fun b : ℤ => sqBracketCoeffZ 2 (n + 1) (b + 1) • W.L b x).Finite := by
  have hg : (Function.support fun i : ℤ =>
      sqBracketCoeffZ 2 (n + 1) i • mode (W.Y W.conformalVector) i x).Finite :=
    sqModeZ_support_finite W W.conformalVector 2 (n + 1) x
  refine Set.Finite.subset (hg.preimage ((add_left_injective (1 : ℤ)).injOn)) ?_
  intro b hb
  simp only [Function.mem_support, ne_eq] at hb
  simp only [Set.mem_preimage, Function.mem_support, ne_eq]
  rw [VertexOperatorAlgebra.L_def] at hb
  exact hb

/-- **The composite `Lω m ∘ Lω n` as a double sum** (outer `b`, inner `a`):
`Lω m (Lω n x) = Σ_b Σ_a (d[m,a]·d[n,b]) • L_a (L_b x)`.  The clean half of the commutator expansion —
push `Lω m` through the finsum (`map_finsum`, `dL_support_finite`), `map_smul`, then `smul_finsum'`. -/
theorem vSqZ_omega_comp (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    vSqZ W W.conformalVector 2 (m + 1) (vSqZ W W.conformalVector 2 (n + 1) x)
      = ∑ᶠ b : ℤ, ∑ᶠ a : ℤ,
          (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
            • W.L a (W.L b x) := by
  rw [vSqZ_omega_apply W n x,
    map_finsum (vSqZ W W.conformalVector 2 (m + 1)) (dL_support_finite W n x)]
  refine finsum_congr (fun b => ?_)
  rw [map_smul, vSqZ_omega_apply W m (W.L b x),
    smul_finsum' (sqBracketCoeffZ 2 (n + 1) (b + 1)) (dL_support_finite W m (W.L b x))]
  refine finsum_congr (fun a => ?_)
  rw [smul_smul, mul_comm]

/-! ## The vacuum square-bracket mode `𝟙[k]` is a scalar (central)

`𝟙₍ᵢ₎ = δ_{i,−1}·id`, so `vSqZ 𝟙 0 k = c(0,k,−1)·id` is a **scalar** operator, hence central.  This is what
makes `⁅Lsq m, Lsq n⁆ = ⁅Lω m, Lω n⁆` (the `ω̃` `𝟙`-terms drop from the commutator), while the `𝟙`-term
in `(m−n)Lsq(m+n)` survives and cancels the `m+n = −2` anomaly. -/

/-- **`𝟙[k] = c(0,k,−1) • id`.**  The vacuum's only nonzero mode is `𝟙₍₋₁₎ = id`, so `vSqZ 𝟙 0 k x =
sqBracketCoeffZ 0 k (−1) • x`.  In particular `𝟙[0] = 0` (`sqBracketCoeffZ 0 0 (−1) = 0`) and `𝟙[k] ≠ 0`
only for `k ≤ −1` (the `k = 0` unit-`zpow` fix makes `c(0,k,−1) = [w^{−1−k}]((1+w)^{−1}u^k)`). -/
theorem vSqZ_vacuum_scalar (W : VertexOperatorAlgebra 𝒱) (k : ℤ) (x : 𝒱) :
    vSqZ W W.vacuum 0 k x = sqBracketCoeffZ 0 k (-1) • x := by
  rw [vSqZ_apply]
  have heq : (fun i : ℤ => sqBracketCoeffZ 0 k i • mode (W.Y W.vacuum) i x)
      = fun i : ℤ => if i = -1 then sqBracketCoeffZ 0 k (-1) • x else 0 := by
    funext i
    rw [W.vacuum_Y, mode_one]
    rcases eq_or_ne i (-1) with rfl | hi
    · simp [Module.End.one_apply]
    · simp [hi]
  rw [heq, finsum_eq_single _ (-1) (fun i hi => if_neg hi), if_pos rfl]

/-- The outer-`b` summand of `Lω m (Lω n x)` equals `Lω m (d[n,b]•L_b x)`, and hence has **finite
support in `b`** (its support `⊆` that of `b ↦ d[n,b]•L_b x`, since `Lω m` is linear).  Needed to split
the commutator subtraction with `finsum_sub_distrib`. -/
theorem dLcomp_support_finite (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (Function.support fun b : ℤ => ∑ᶠ a : ℤ,
      (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
        • W.L a (W.L b x)).Finite := by
  have hval : ∀ b : ℤ, (∑ᶠ a : ℤ,
      (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)) • W.L a (W.L b x))
      = (vSqZ W W.conformalVector 2 (m + 1)) (sqBracketCoeffZ 2 (n + 1) (b + 1) • W.L b x) := by
    intro b
    rw [map_smul, vSqZ_omega_apply W m (W.L b x),
      smul_finsum' (sqBracketCoeffZ 2 (n + 1) (b + 1)) (dL_support_finite W m (W.L b x))]
    exact finsum_congr (fun a => by rw [smul_smul, mul_comm])
  simp only [hval]
  refine (dL_support_finite W n x).subset ?_
  intro b hb
  simp only [Function.mem_support, ne_eq] at hb ⊢
  intro hzero
  exact hb (by rw [hzero, map_zero])

/-- Finite support in `a` of `a ↦ (d[p,a]·c) • L_a y` (support `⊆` that of `a ↦ d[p,a]•L_a y`, the
constant `c` doesn't enlarge it).  The inner-`a` support for the commutator subtraction. -/
theorem dLmul_support_finite (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (c : ℂ) (y : 𝒱) :
    (Function.support fun a : ℤ => (sqBracketCoeffZ 2 (p + 1) (a + 1) * c) • W.L a y).Finite := by
  refine (dL_support_finite W p y).subset ?_
  intro a ha
  simp only [Function.mem_support, ne_eq] at ha ⊢
  intro hz
  exact ha (by rw [show (sqBracketCoeffZ 2 (p + 1) (a + 1) * c) • W.L a y
      = c • (sqBracketCoeffZ 2 (p + 1) (a + 1) • W.L a y) from by rw [smul_smul, mul_comm],
    hz, smul_zero])

/-- **The commutator of the `ω`-modes as a single double sum** (`b` outer, `a` inner):
`⁅Lω m, Lω n⁆ x = Σ_b Σ_a (d[m,a]d[n,b] − d[n,a]d[m,b]) • L_a(L_b x)`.  (Applied form; the two
composites `vSqZ_omega_comp` subtracted, distributing `finsum_sub_distrib` over both indices.) -/
theorem vSqZ_omega_commutator (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (vSqZ W W.conformalVector 2 (m + 1)) ((vSqZ W W.conformalVector 2 (n + 1)) x)
      - (vSqZ W W.conformalVector 2 (n + 1)) ((vSqZ W W.conformalVector 2 (m + 1)) x)
      = ∑ᶠ b : ℤ, ∑ᶠ a : ℤ,
          ((sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
            - (sqBracketCoeffZ 2 (n + 1) (a + 1) * sqBracketCoeffZ 2 (m + 1) (b + 1)))
            • W.L a (W.L b x) := by
  rw [vSqZ_omega_comp W m n x, vSqZ_omega_comp W n m x,
    ← finsum_sub_distrib (dLcomp_support_finite W m n x) (dLcomp_support_finite W n m x)]
  refine finsum_congr (fun b => ?_)
  rw [← finsum_sub_distrib (dLmul_support_finite W m (sqBracketCoeffZ 2 (n + 1) (b + 1)) (W.L b x))
    (dLmul_support_finite W n (sqBracketCoeffZ 2 (m + 1) (b + 1)) (W.L b x))]
  exact finsum_congr (fun a => by rw [← sub_smul])

/-- **The joint (rectangle) support** of `p ↦ (d[m,p.1]·d[n,p.2]) • L_{p.1}(L_{p.2} x)` is finite —
a finite biUnion: `p.2` ranges over the finite `dL(n,x)`-support, and for each such `p.2`, `p.1` ranges
over the finite `dL(m, L_{p.2} x)`-support (the union-not-rectangle crux).  Needed for the `a↔b` swap. -/
theorem jointSupport_finite (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (Function.support fun p : ℤ × ℤ =>
      (sqBracketCoeffZ 2 (m + 1) (p.1 + 1) * sqBracketCoeffZ 2 (n + 1) (p.2 + 1))
        • W.L p.1 (W.L p.2 x)).Finite := by
  refine Set.Finite.subset
    ((dL_support_finite W n x).biUnion (fun b _ =>
      (dL_support_finite W m (W.L b x)).image (fun a => (a, b)))) ?_
  intro p hp
  simp only [Function.mem_support, ne_eq, smul_ne_zero_iff, mul_ne_zero_iff] at hp
  obtain ⟨⟨hm, hn⟩, hvec⟩ := hp
  simp only [Set.mem_iUnion, Set.mem_image, Function.mem_support, ne_eq, smul_ne_zero_iff,
    exists_prop]
  refine ⟨p.2, ⟨hn, fun h => hvec (by rw [h, map_zero])⟩, p.1, ⟨hm, hvec⟩, rfl⟩

/-! ## FORM B — the commutator as `Σ_a Σ_b d[m,a]d[n,b] • ⁅L a, L b⁆`

The key simplification: the *outer* sums collapse **directly** through `vSqZ_omega_apply` (no `a↔b`
swap is needed), because the inner sums evaluate to `d[m,a] • L_a((Lω n)x)` and `d[m,a] • (Lω n)(L_a x)`
— both of the shape `d[p,·] • T(L_· y)` for a linear `T`.  So one reusable lemma (`dLT_finsum`, pushing a
linear map through the `dL`-finsum) does all the work. -/

/-- Finite support of `b ↦ d[p,b] • T (L_b y)` for linear `T` (the reusable support bound: `T` cannot
enlarge the support, since `d[p,b] • T(L_b y) = T(d[p,b] • L_b y)`). -/
theorem support_finite_of_dLT (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (T : 𝒱 →ₗ[ℂ] 𝒱) (y : 𝒱) :
    (Function.support fun b : ℤ => sqBracketCoeffZ 2 (p + 1) (b + 1) • T (W.L b y)).Finite := by
  refine (dL_support_finite W p y).subset ?_
  intro b hb
  simp only [Function.mem_support, ne_eq] at hb ⊢
  intro hz
  exact hb (by rw [← map_smul, hz, map_zero])

/-- Finite support of `b ↦ (c·d[p,b]) • L_b y` (a scalar factor cannot enlarge the support). -/
theorem support_finite_of_dLc (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (c : ℂ) (y : 𝒱) :
    (Function.support fun b : ℤ => (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • W.L b y).Finite := by
  refine (dL_support_finite W p y).subset ?_
  intro b hb
  simp only [Function.mem_support, ne_eq] at hb ⊢
  intro hz
  exact hb (by rw [show (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • W.L b y
      = c • (sqBracketCoeffZ 2 (p + 1) (b + 1) • W.L b y) from by rw [smul_smul], hz, smul_zero])

/-- Finite support of `b ↦ (c·d[p,b]) • T (L_b y)`. -/
theorem support_finite_of_dLcT (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (c : ℂ)
    (T : 𝒱 →ₗ[ℂ] 𝒱) (y : 𝒱) :
    (Function.support fun b : ℤ =>
      (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • T (W.L b y)).Finite := by
  refine (dL_support_finite W p y).subset ?_
  intro b hb
  simp only [Function.mem_support, ne_eq] at hb ⊢
  intro hz
  exact hb (by rw [show (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • T (W.L b y)
      = c • T (sqBracketCoeffZ 2 (p + 1) (b + 1) • W.L b y) from by rw [map_smul, smul_smul],
    hz, map_zero, smul_zero])

/-- **Pushing a linear map through the `dL`-finsum:** `Σ_b d[p,b] • T(L_b y) = T((Lω p) y)`.
The workhorse of Form B (instantiated at `T = W.L a` and `T = Lω n`). -/
theorem dLT_finsum (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (T : 𝒱 →ₗ[ℂ] 𝒱) (y : 𝒱) :
    (∑ᶠ b : ℤ, sqBracketCoeffZ 2 (p + 1) (b + 1) • T (W.L b y))
      = T ((vSqZ W W.conformalVector 2 (p + 1)) y) := by
  rw [vSqZ_omega_apply W p y, map_finsum T (dL_support_finite W p y)]
  exact finsum_congr (fun b => (map_smul T _ _).symm)

/-- The scalar-weighted version of `vSqZ_omega_apply`: `Σ_b (c·d[p,b]) • L_b y = c • (Lω p) y`. -/
theorem dLc_finsum (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (c : ℂ) (y : 𝒱) :
    (∑ᶠ b : ℤ, (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • W.L b y)
      = c • (vSqZ W W.conformalVector 2 (p + 1)) y := by
  rw [vSqZ_omega_apply W p y, smul_finsum' c (dL_support_finite W p y)]
  exact finsum_congr (fun b => by rw [smul_smul])

/-- The scalar-weighted version of `dLT_finsum`: `Σ_b (c·d[p,b]) • T(L_b y) = c • T((Lω p) y)`. -/
theorem dLcT_finsum (W : VertexOperatorAlgebra 𝒱) (p : ℤ) (c : ℂ) (T : 𝒱 →ₗ[ℂ] 𝒱) (y : 𝒱) :
    (∑ᶠ b : ℤ, (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • T (W.L b y))
      = c • T ((vSqZ W W.conformalVector 2 (p + 1)) y) := by
  calc (∑ᶠ b : ℤ, (c * sqBracketCoeffZ 2 (p + 1) (b + 1)) • T (W.L b y))
      = ∑ᶠ b : ℤ, c • (sqBracketCoeffZ 2 (p + 1) (b + 1) • T (W.L b y)) :=
        finsum_congr (fun b => by rw [smul_smul])
    _ = c • ∑ᶠ b : ℤ, sqBracketCoeffZ 2 (p + 1) (b + 1) • T (W.L b y) :=
        (smul_finsum' c (support_finite_of_dLT W p T y)).symm
    _ = c • T ((vSqZ W W.conformalVector 2 (p + 1)) y) := by rw [dLT_finsum]

/-- `⁅L a, L b⁆ y = L_a(L_b y) − L_b(L_a y)` (the `Module.End` ring commutator, applied). -/
theorem lie_L_apply (W : VertexOperatorAlgebra 𝒱) (a b : ℤ) (y : 𝒱) :
    ⁅W.L a, W.L b⁆ y = W.L a (W.L b y) - W.L b (W.L a y) := by
  rw [Ring.lie_def]
  rfl

/-- **FORM B** — the `ω`-mode commutator as Gannon's double sum over the *ordinary* Virasoro
commutators: `⁅Lω m, Lω n⁆ x = Σ_a Σ_b d[m,a]·d[n,b] • ⁅L a, L b⁆ x`.  This is the form that
`L_virasoro` plugs into. -/
theorem vSqZ_omega_lie (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (vSqZ W W.conformalVector 2 (m + 1)) ((vSqZ W W.conformalVector 2 (n + 1)) x)
      - (vSqZ W W.conformalVector 2 (n + 1)) ((vSqZ W W.conformalVector 2 (m + 1)) x)
      = ∑ᶠ a : ℤ, ∑ᶠ b : ℤ,
          (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
            • ⁅W.L a, W.L b⁆ x := by
  -- the inner (`b`) sum, for each `a`
  have hinner : ∀ a : ℤ,
      (∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
          • ⁅W.L a, W.L b⁆ x)
        = sqBracketCoeffZ 2 (m + 1) (a + 1)
            • W.L a ((vSqZ W W.conformalVector 2 (n + 1)) x)
          - sqBracketCoeffZ 2 (m + 1) (a + 1)
            • (vSqZ W W.conformalVector 2 (n + 1)) (W.L a x) := by
    intro a
    rw [← dLcT_finsum W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a) x,
      ← dLc_finsum W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a x),
      ← finsum_sub_distrib
        (support_finite_of_dLcT W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a) x)
        (support_finite_of_dLc W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a x))]
    exact finsum_congr (fun b => by rw [lie_L_apply, smul_sub])
  rw [finsum_congr hinner,
    finsum_sub_distrib
      (dL_support_finite W m ((vSqZ W W.conformalVector 2 (n + 1)) x))
      (support_finite_of_dLT W m (vSqZ W W.conformalVector 2 (n + 1)) x),
    ← vSqZ_omega_apply W m ((vSqZ W W.conformalVector 2 (n + 1)) x),
    dLT_finsum W m (vSqZ W W.conformalVector 2 (n + 1)) x]

/-! ## TASK 2 — the assembly: `L_virasoro` inside the double sum

Feeding `L_virasoro` into Form B splits the summand into a **bracket** part `((a:ℂ)−b)•L_{a+b}` and a
**central** part `δ_{a+b,0}·((a³−a)/12·c)•id`.  The bracket part collapses by
`sqBracketCoeff_witt_identity` (with `j := a+b`, where the identity's weight `2a−j` is exactly `a−b`);
the central part becomes the scalar `centralMoment` — the Gel'fand–Fuks cocycle. -/

/-- The inner (`b`) sum of the commutator expansion at fixed `a` (the standalone form of the step
inside `vSqZ_omega_lie`). -/
theorem vSqZ_omega_inner (W : VertexOperatorAlgebra 𝒱) (m n a : ℤ) (x : 𝒱) :
    (∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
        • ⁅W.L a, W.L b⁆ x)
      = sqBracketCoeffZ 2 (m + 1) (a + 1) • W.L a ((vSqZ W W.conformalVector 2 (n + 1)) x)
        - sqBracketCoeffZ 2 (m + 1) (a + 1)
          • (vSqZ W W.conformalVector 2 (n + 1)) (W.L a x) := by
  rw [← dLcT_finsum W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a) x,
    ← dLc_finsum W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a x),
    ← finsum_sub_distrib
      (support_finite_of_dLcT W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a) x)
      (support_finite_of_dLc W n (sqBracketCoeffZ 2 (m + 1) (a + 1)) (W.L a x))]
  exact finsum_congr (fun b => by rw [lie_L_apply, smul_sub])

/-- **The central moment** `S(m,n) = Σ_a d[m,a]·d[n,−a]·(a³−a)` — the Gel'fand–Fuks cocycle of the
square-bracket modes.  Engine-verified closed form (`certificates/mathematica`, exact rationals):
`S(m,n) = (m³−m)·δ_{m+n,0} − ((m−n)/2)·δ_{m+n,−2}` — the `δ_{m+n,−2}` anomaly is **real**, and is exactly
what the `ω̃` vacuum term of `Lsq` cancels. -/
noncomputable def centralMoment (m n : ℤ) : ℂ :=
  ∑ᶠ a : ℤ, sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((-a) + 1)
    * (((a ^ 3 - a : ℤ)) : ℂ)

/-- The coefficient family `a ↦ d[m,a]·d[n,j−a]·(2a−j)` has finite support (`⊆ Icc m (j−n)`) — the
lower-triangularity of `d` on both factors.  (Also the support used inside
`sqBracketCoeff_witt_identity`.) -/
theorem coeffProd_support_finite (m n j : ℤ) :
    (Function.support fun a : ℤ => sqBracketCoeffZ 2 (m + 1) (a + 1)
      * sqBracketCoeffZ 2 (n + 1) ((j - a) + 1) * (((2 * a - j : ℤ)) : ℂ)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc m (j - n)) ?_
  intro a ha
  simp only [Function.mem_support, ne_eq] at ha
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    push_neg at h
    exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul])
  · by_contra h
    push_neg at h
    exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show (j - a) + 1 < n + 1 by omega), mul_zero, zero_mul])

/-- The central family `a ↦ d[m,a]·d[n,−a]·(a³−a)` has finite support (`⊆ Icc m (−n)`), so
`centralMoment` is a genuine finite sum. -/
theorem centralMoment_support_finite (m n : ℤ) :
    (Function.support fun a : ℤ => sqBracketCoeffZ 2 (m + 1) (a + 1)
      * sqBracketCoeffZ 2 (n + 1) ((-a) + 1) * (((a ^ 3 - a : ℤ)) : ℂ)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc m (-n)) ?_
  intro a ha
  simp only [Function.mem_support, ne_eq] at ha
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    push_neg at h
    exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul])
  · by_contra h
    push_neg at h
    exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show (-a) + 1 < n + 1 by omega), mul_zero, zero_mul])

/-- The inner bracket sum, reindexed `b ↦ j = a+b` (so the weight `(a:ℂ)−b` becomes the identity's
`2a−j`). -/
theorem bracketInner_reindex (W : VertexOperatorAlgebra 𝒱) (m n a : ℤ) (x : 𝒱) :
    (∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)
        * ((a : ℂ) - (b : ℂ))) • W.L (a + b) x)
      = ∑ᶠ j : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((j - a) + 1)
        * (((2 * a - j : ℤ)) : ℂ)) • W.L j x := by
  refine finsum_eq_of_bijective (fun b => a + b)
    ⟨fun b1 b2 h => by dsimp only at h; omega, fun j => ⟨j - a, by dsimp only; omega⟩⟩ (fun b => ?_)
  have hs : (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)
        * ((a : ℂ) - (b : ℂ)))
      = (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (((a + b) - a) + 1)
        * (((2 * a - (a + b) : ℤ)) : ℂ)) := by
    rw [show (a + b) - a = b from by ring, show (2 * a - (a + b) : ℤ) = a - b from by ring]
    push_cast
    ring
  rw [hs]

/-- **The joint (rectangle) support** of the reindexed bracket family — from `W.regularity` (bounding
`j` above) plus lower-triangularity of `d` in both factors (bounding `a` below by `m` and `j` below by
`m+n`). -/
theorem bracketJoint_support_finite (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (Function.support fun p : ℤ × ℤ =>
      (sqBracketCoeffZ 2 (m + 1) (p.1 + 1) * sqBracketCoeffZ 2 (n + 1) ((p.2 - p.1) + 1)
        * (((2 * p.1 - p.2 : ℤ)) : ℂ)) • W.L p.2 x).Finite := by
  obtain ⟨N, hN⟩ := W.regularity W.conformalVector x
  refine Set.Finite.subset
    (Set.Finite.prod (Set.finite_Icc m (N - n)) (Set.finite_Icc (m + n) N)) ?_
  intro p hp
  simp only [Function.mem_support, ne_eq, smul_ne_zero_iff] at hp
  obtain ⟨hc, hv⟩ := hp
  have hm : m ≤ p.1 := by
    by_contra h
    push_neg at h
    exact hc (by rw [sqBracketCoeffZ_of_lt 2 (show p.1 + 1 < m + 1 by omega), zero_mul, zero_mul])
  have hn : n ≤ p.2 - p.1 := by
    by_contra h
    push_neg at h
    exact hc (by
      rw [sqBracketCoeffZ_of_lt 2 (show (p.2 - p.1) + 1 < n + 1 by omega), mul_zero, zero_mul])
  have hj : p.2 + 1 < N := by
    by_contra h
    push_neg at h
    exact hv (by rw [VertexOperatorAlgebra.L_def]; exact hN (p.2 + 1) h)
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨hm, by omega⟩, ⟨by omega, by omega⟩⟩

/-- **The bracket half collapses:** `Σ_a Σ_b d[m,a]d[n,b]·(a−b) • L_{a+b} x = (m−n) • Lω(m+n) x`.
Reindex `b ↦ j = a+b`, swap (`finsum_finsum_comm` + the rectangle support), pull the vector out, and
apply `sqBracketCoeff_witt_identity` — the whole point of B(i). -/
theorem bracketDouble_collapse (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (∑ᶠ a : ℤ, ∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)
        * ((a : ℂ) - (b : ℂ))) • W.L (a + b) x)
      = ((m - n : ℤ) : ℂ) • (vSqZ W W.conformalVector 2 (m + n + 1)) x := by
  rw [finsum_congr (fun a => bracketInner_reindex W m n a x),
    ← finsum_finsum_comm _ (bracketJoint_support_finite W m n x),
    ← dLc_finsum W (m + n) ((m - n : ℤ) : ℂ) x]
  refine finsum_congr (fun j => ?_)
  rw [← finsum_smul' (coeffProd_support_finite m n j) (W.L j x),
    sqBracketCoeff_witt_identity m n j]

/-- `L_virasoro` in applied form. -/
theorem L_virasoro_apply (W : VertexOperatorAlgebra 𝒱) (a b : ℤ) (y : 𝒱) :
    ⁅W.L a, W.L b⁆ y = ((a : ℂ) - (b : ℂ)) • W.L (a + b) y
      + (if a + b = 0 then (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge) • y else 0) := by
  have h := congrArg (fun T : Module.End ℂ 𝒱 => T y) (W.L_virasoro a b)
  by_cases hab : a + b = 0 <;> simpa [hab] using h

/-- If a doubly-indexed family has finite joint support, then `a ↦ Σ_j G a j` has finite support
(contained in the first projection of the joint support). -/
theorem support_finsum_fst {M : Type*} [AddCommMonoid M] (G : ℤ → ℤ → M)
    (hG : (Function.support fun p : ℤ × ℤ => G p.1 p.2).Finite) :
    (Function.support fun a : ℤ => ∑ᶠ j : ℤ, G a j).Finite := by
  refine (hG.image Prod.fst).subset ?_
  intro a ha
  simp only [Function.mem_support, ne_eq] at ha
  by_contra hc
  refine ha ?_
  have hzero : ∀ j : ℤ, G a j = 0 := by
    intro j
    by_contra hz
    exact hc ⟨(a, j), by simpa only [Function.mem_support, ne_eq] using hz, rfl⟩
  simp only [hzero, finsum_zero]

/-- Finite support (in `b`) of the bracket part at fixed `a` — `d[n,·]` bounds below, `W.regularity`
above. -/
theorem bracketInner_support_finite (W : VertexOperatorAlgebra 𝒱) (m n a : ℤ) (x : 𝒱) :
    (Function.support fun b : ℤ => (sqBracketCoeffZ 2 (m + 1) (a + 1)
      * sqBracketCoeffZ 2 (n + 1) (b + 1) * ((a : ℂ) - (b : ℂ))) • W.L (a + b) x).Finite := by
  obtain ⟨N, hN⟩ := W.regularity W.conformalVector x
  refine Set.Finite.subset (Set.finite_Ico n (N - a)) ?_
  intro b hb
  simp only [Function.mem_support, ne_eq, smul_ne_zero_iff] at hb
  obtain ⟨hc, hv⟩ := hb
  simp only [Set.mem_Ico]
  constructor
  · by_contra h
    push_neg at h
    exact hc (by rw [sqBracketCoeffZ_of_lt 2 (show b + 1 < n + 1 by omega), mul_zero, zero_mul])
  · by_contra h
    push_neg at h
    exact hv (by rw [VertexOperatorAlgebra.L_def]; exact hN (a + b + 1) (by omega))

/-- Finite support (in `b`) of the central part at fixed `a` — it lives on the single point `b = −a`. -/
theorem centralInner_support_finite (W : VertexOperatorAlgebra 𝒱) (m n a : ℤ) (x : 𝒱) :
    (Function.support fun b : ℤ => (sqBracketCoeffZ 2 (m + 1) (a + 1)
      * sqBracketCoeffZ 2 (n + 1) (b + 1))
      • (if a + b = 0 then (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge) • x
         else (0 : 𝒱))).Finite := by
  refine Set.Finite.subset (Set.finite_singleton (-a)) ?_
  intro b hb
  simp only [Function.mem_support, ne_eq] at hb
  simp only [Set.mem_singleton_iff]
  by_contra hc
  exact hb (by rw [if_neg (by omega), smul_zero])

/-- The central inner sum collapses to its single term `b = −a`. -/
theorem centralInner_collapse (W : VertexOperatorAlgebra 𝒱) (m n a : ℤ) (x : 𝒱) :
    (∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
      • (if a + b = 0 then (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge) • x else (0 : 𝒱)))
      = (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((-a) + 1)
          * (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge)) • x := by
  rw [finsum_eq_single _ (-a) (fun b hb => by rw [if_neg (by omega), smul_zero]),
    if_pos (by omega), smul_smul]

/-- The scalar central family has finite support (`⊆ Icc m (−n)`). -/
theorem centralCoeff_support_finite (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) :
    (Function.support fun a : ℤ => sqBracketCoeffZ 2 (m + 1) (a + 1)
      * sqBracketCoeffZ 2 (n + 1) ((-a) + 1)
      * (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge)).Finite := by
  refine Set.Finite.subset (Set.finite_Icc m (-n)) ?_
  intro a ha
  simp only [Function.mem_support, ne_eq] at ha
  simp only [Set.mem_Icc]
  constructor
  · by_contra h
    push_neg at h
    exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul])
  · by_contra h
    push_neg at h
    exact ha (by rw [sqBracketCoeffZ_of_lt 2 (show (-a) + 1 < n + 1 by omega), mul_zero, zero_mul])

/-- **The `ω`-mode torus-Virasoro relation** — the bracket half assembled, with the central term
the named scalar `centralMoment`:
`⁅Lω m, Lω n⁆ x = (m−n) • Lω(m+n) x + ((c/12)·S(m,n)) • x`.
(`S(m,n) = centralMoment m n`; its closed form `(m³−m)δ_{m+n,0} − ((m−n)/2)δ_{m+n,−2}` is the
Gel'fand–Fuks cocycle — engine-verified, formalization named separately.) -/
theorem vSqZ_omega_virasoro (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    (vSqZ W W.conformalVector 2 (m + 1)) ((vSqZ W W.conformalVector 2 (n + 1)) x)
      - (vSqZ W W.conformalVector 2 (n + 1)) ((vSqZ W W.conformalVector 2 (m + 1)) x)
      = ((m - n : ℤ) : ℂ) • (vSqZ W W.conformalVector 2 (m + n + 1)) x
        + ((W.centralCharge / 12) * centralMoment m n) • x := by
  rw [vSqZ_omega_lie W m n x]
  have hpt : ∀ a b : ℤ,
      (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
          • ⁅W.L a, W.L b⁆ x
        = (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)
            * ((a : ℂ) - (b : ℂ))) • W.L (a + b) x
          + (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
            • (if a + b = 0 then (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge) • x
               else (0 : 𝒱)) := by
    intro a b
    rw [L_virasoro_apply, smul_add, smul_smul]
  have hinner : ∀ a : ℤ,
      (∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1))
          • ⁅W.L a, W.L b⁆ x)
        = (∑ᶠ b : ℤ, (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)
            * ((a : ℂ) - (b : ℂ))) • W.L (a + b) x)
          + (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((-a) + 1)
              * (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge)) • x := by
    intro a
    rw [finsum_congr (fun b => hpt a b),
      finsum_add_distrib (bracketInner_support_finite W m n a x)
        (centralInner_support_finite W m n a x),
      centralInner_collapse]
  have hbrOuter : (Function.support fun a : ℤ => ∑ᶠ b : ℤ,
      (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) (b + 1)
        * ((a : ℂ) - (b : ℂ))) • W.L (a + b) x).Finite := by
    simp only [bracketInner_reindex W m n _ x]
    exact support_finsum_fst _ (bracketJoint_support_finite W m n x)
  have hceOuter : (Function.support fun a : ℤ =>
      (sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((-a) + 1)
        * (((a : ℂ) ^ 3 - (a : ℂ)) / 12 * W.centralCharge)) • x).Finite := by
    refine (centralCoeff_support_finite W m n).subset ?_
    intro a ha
    simp only [Function.mem_support, ne_eq] at ha ⊢
    intro hz
    exact ha (by rw [hz, zero_smul])
  rw [finsum_congr hinner, finsum_add_distrib hbrOuter hceOuter,
    bracketDouble_collapse W m n x,
    ← finsum_smul' (centralCoeff_support_finite W m n) x]
  congr 2
  rw [centralMoment, mul_finsum' _ _ (centralMoment_support_finite m n)]
  exact finsum_congr (fun a => by push_cast; ring)

/-! ## TASK 3 (partial) — the central moment `S(m,n)`

The closed form `S(m,n) = (m³−m)δ_{m+n,0} − ((m−n)/2)δ_{m+n,−2}` is engine-verified in exact rationals
(0 mismatches over all 1369 pairs `m,n ∈ [−18,18]`; closed form `S(m,n) = Res_w(f_m‴·f_n)` with
`f_m = (1+w)(log(1+w))^{m+1}`, constant exactly `1`).  The two cases where the summation window
`Icc m (−n)` is empty or a singleton are proved here; the `m+n < 0` cases are the deep Gel'fand–Fuks
content (carried as the named hypothesis `CentralMomentClosed`). -/

/-- **`S(m,n) = 0` for `m+n > 0`** — the summation window `Icc m (−n)` is empty. -/
theorem centralMoment_of_pos (m n : ℤ) (h : 0 < m + n) : centralMoment m n = 0 := by
  rw [centralMoment]
  have hz : ∀ a : ℤ, sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 (n + 1) ((-a) + 1)
      * (((a ^ 3 - a : ℤ)) : ℂ) = 0 := by
    intro a
    by_cases ha : m ≤ a
    · rw [sqBracketCoeffZ_of_lt 2 (show (-a) + 1 < n + 1 by omega), mul_zero, zero_mul]
    · push_neg at ha
      rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul]
  simp only [hz, finsum_zero]

/-- **`S(m,−m) = m³ − m`** — the `m+n = 0` case collapses to the single diagonal term `a = m`
(`d[m,m] = d[−m,−m] = 1`).  This is the standard Virasoro central term. -/
theorem centralMoment_of_zero (m : ℤ) : centralMoment m (-m) = ((m : ℂ)) ^ 3 - (m : ℂ) := by
  have hsingle : ∀ a : ℤ, a ≠ m →
      sqBracketCoeffZ 2 (m + 1) (a + 1) * sqBracketCoeffZ 2 ((-m) + 1) ((-a) + 1)
        * (((a ^ 3 - a : ℤ)) : ℂ) = 0 := by
    intro a ha
    by_cases h : a < m
    · rw [sqBracketCoeffZ_of_lt 2 (show a + 1 < m + 1 by omega), zero_mul, zero_mul]
    · push_neg at h
      rw [sqBracketCoeffZ_of_lt 2 (show (-a) + 1 < (-m) + 1 by omega), mul_zero, zero_mul]
  rw [centralMoment, finsum_eq_single _ m hsingle, sqBracketCoeffZ_diag m,
    sqBracketCoeffZ_diag (-m)]
  push_cast
  ring

/-- **The Gel'fand–Fuks closed form** of the central moment (engine-verified in exact rationals;
`m+n ≥ 0` cases proved above as `centralMoment_of_pos`/`centralMoment_of_zero`).  Carried as a named
hypothesis for the `m+n < 0` cases — the deep remaining content of GOAL B. -/
def CentralMomentClosed : Prop :=
  ∀ m n : ℤ, centralMoment m n
    = (if m + n = 0 then ((m : ℂ) ^ 3 - (m : ℂ)) else 0)
      - (if m + n = -2 then (((m : ℂ) - (n : ℂ)) / 2) else 0)

/-! ## TASK 4 — from `Lω` to `Lsq` (the `ω̃` vacuum term) -/

/-- `Lsq n` in applied form: the `𝟙`-part is the **scalar** `(c/24)·s(n+1)` (`vSqZ_vacuum_scalar`). -/
theorem Lsq_apply (W : VertexOperatorAlgebra 𝒱) (n : ℤ) (x : 𝒱) :
    Lsq W n x = (vSqZ W W.conformalVector 2 (n + 1)) x
      - ((W.centralCharge / 24) * sqBracketCoeffZ 0 (n + 1) (-1)) • x := by
  show (vSqZ W W.conformalVector 2 (n + 1) - (W.centralCharge / 24) • vSqZ W W.vacuum 0 (n + 1)) x
    = _
  rw [LinearMap.sub_apply, LinearMap.smul_apply, vSqZ_vacuum_scalar, smul_smul]

/-- The `𝟙`-terms of `Lsq` are **scalars**, hence cancel from the commutator:
`⁅Lsq m, Lsq n⁆ x = ⁅Lω m, Lω n⁆ x`. -/
theorem Lsq_commutator_eq_omega (W : VertexOperatorAlgebra 𝒱) (m n : ℤ) (x : 𝒱) :
    Lsq W m (Lsq W n x) - Lsq W n (Lsq W m x)
      = (vSqZ W W.conformalVector 2 (m + 1)) ((vSqZ W W.conformalVector 2 (n + 1)) x)
        - (vSqZ W W.conformalVector 2 (n + 1)) ((vSqZ W W.conformalVector 2 (m + 1)) x) := by
  have hcomp : ∀ p q : ℤ, Lsq W p (Lsq W q x)
      = (vSqZ W W.conformalVector 2 (p + 1)) ((vSqZ W W.conformalVector 2 (q + 1)) x)
        - ((W.centralCharge / 24) * sqBracketCoeffZ 0 (q + 1) (-1))
            • (vSqZ W W.conformalVector 2 (p + 1)) x
        - ((W.centralCharge / 24) * sqBracketCoeffZ 0 (p + 1) (-1))
            • (vSqZ W W.conformalVector 2 (q + 1)) x
        + (((W.centralCharge / 24) * sqBracketCoeffZ 0 (p + 1) (-1))
            * ((W.centralCharge / 24) * sqBracketCoeffZ 0 (q + 1) (-1))) • x := by
    intro p q
    rw [Lsq_apply W q x, Lsq_apply W p _, map_sub, map_smul, smul_sub, smul_smul]
    abel
  rw [hcomp m n, hcomp n m,
    mul_comm ((W.centralCharge / 24) * sqBracketCoeffZ 0 (n + 1) (-1))
      ((W.centralCharge / 24) * sqBracketCoeffZ 0 (m + 1) (-1))]
  abel

/-- **THE SQUARE-BRACKET VIRASORO RELATION** (Gannon 5.3.15 / Zhu §4):
`⁅L[m], L[n]⁆ = (m−n)·L[m+n] + δ_{m+n,0}·((m³−m)/12)·c·id` — the **same central charge `c`**.

The `ω̃` vacuum term is essential: the `ω`-only modes carry the Schwarzian anomaly
`−((m−n)/2)δ_{m+n,−2}` in their central moment, and the `𝟙[−1] = id` term of `Lsq` cancels it exactly
(here: `sqBracketCoeffZ_vacuum_neg_one` against the `m+n = −2` branch of `CentralMomentClosed`).

Carries the single named hypothesis `CentralMomentClosed` (the Gel'fand–Fuks closed form of
`centralMoment`, engine-verified; its `m+n ≥ 0` cases are *proved* — `centralMoment_of_pos`,
`centralMoment_of_zero`). -/
theorem Lsq_virasoro_apply (W : VertexOperatorAlgebra 𝒱) (hCM : CentralMomentClosed)
    (m n : ℤ) (x : 𝒱) :
    Lsq W m (Lsq W n x) - Lsq W n (Lsq W m x)
      = ((m - n : ℤ) : ℂ) • Lsq W (m + n) x
        + (if m + n = 0 then (((m : ℂ) ^ 3 - (m : ℂ)) / 12 * W.centralCharge) else 0) • x := by
  have hscalar : (W.centralCharge / 12) * centralMoment m n
      = -(((m - n : ℤ) : ℂ)
            * ((W.centralCharge / 24) * sqBracketCoeffZ 0 ((m + n) + 1) (-1)))
        + (if m + n = 0 then (((m : ℂ) ^ 3 - (m : ℂ)) / 12 * W.centralCharge) else 0) := by
    rw [hCM m n]
    by_cases h0 : m + n = 0
    · rw [if_pos h0, if_pos h0, if_neg (show ¬(m + n = -2) by omega),
        sqBracketCoeffZ_vacuum_of_ne ((m + n) + 1) (by omega)]
      ring
    · by_cases h2 : m + n = -2
      · rw [if_neg h0, if_neg h0, if_pos h2,
          show (m + n) + 1 = (-1 : ℤ) from by omega, sqBracketCoeffZ_vacuum_neg_one]
        push_cast
        ring
      · rw [if_neg h0, if_neg h0, if_neg h2,
          sqBracketCoeffZ_vacuum_of_ne ((m + n) + 1) (by omega)]
        ring
  rw [Lsq_commutator_eq_omega, vSqZ_omega_virasoro, Lsq_apply W (m + n) x, smul_sub, smul_smul,
    hscalar, add_smul, neg_smul]
  abel

end VOA
