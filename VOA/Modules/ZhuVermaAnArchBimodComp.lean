/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAnmIdeal
import VOA.Modules.ZhuVermaAnArchAnIdeal
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The Dong–Jiang bimodule composition `A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱) → A_{p,m}(𝒱)`

This file constructs the **central composition map** of the Dong–Jiang bimodule layer
(Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259 (2008) 799–826,
`math/0601626`, §3 Prop. 3.4) — the engine for the `V̂`-representation action that makes the induced
module `M(U) = ⊕ₙ A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` a `𝒱`-module (Gannon Thm 5.3.4).

## The composition product on `𝒱`

For homogeneous `u ∈ 𝒱_k`, the Dong–Jiang composition (DJ §3) is the residue product carrying the
**source level pair `(p, n)`** of the left factor onto the **target level pair `(p, m)`**:

  `u *^{p,n,m} v = ∑_{i=0}^{m} (-1)^i C(p+i, i) · Res_z (1+z)^{k+m}/z^{p+i+1} Y(u,z)v`
                `= anmRight W p m u v`,

the `A_{p,m}(𝒱)` right-action formula (shift `s = m`, binomial `p+i`, pole `p+i+1`, range `m+1`).
The middle level `n` is the level over which the two factors are **balanced** (the `A_n(𝒱)`-action of
`A_{p,n}` on the right matches the `A_n(𝒱)`-action of `A_{n,m}` on the left); it does not change the
residue formula but is recorded in the level data, so we name the composition
`anmCompose W p n m := anmRight W p m`.

Engine sanity (rank-1 free boson, `certificates/mathematica/comp_check.wl`): the diagonal `(0,0,0)`
collapses to the Zhu product (`anmRight W 0 0 = zhuMul`), and `(n,n,n)` to the `A_n(𝒱)` product
(`anmRight W n n`), matching DJ Prop. 4.6 `A_{n,n} = A_n`.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `anmCompose W p n m` — the composition product on `𝒱` (`= anmRight W p m`), with full ℂ-bilinearity
  (`anmCompose_add_left/smul_left/add_right/smul_right`) and the anchor identifications
  (`anmCompose_diag_eq_anmRight`, `anmCompose_zero_zero_zero`).
* `anmComposeL`/`anmComposeR` — the two single-slot ℂ-linear maps `u ↦ u *^{p,n,m} v` and
  `v ↦ u *^{p,n,m} v` (for the `span_le`/`comap`/`liftQ` descents).
* **`AnmComposeDescL`/`AnmComposeDescR`** — the two precise descent `Prop`s (DJ Lemma 2.8 / Prop 3.4
  well-definedness): the composition carries `O_{p,n}` (left slot) and `O_{n,m}` (right slot) into the
  target `O_{p,m}`; each reduced to its generator families (`AnmComposeDescL_of_gens`,
  `AnmComposeDescR_of_gens`).
* **`anmComposeBilin`** — the **descended ℂ-bilinear composition map**
  `A_{p,n}(𝒱) →ₗ A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)`, `[u] ↦ [v] ↦ [u *^{p,n,m} v]`, conditional ONLY on the
  two descent `Prop`s, with the representative-evaluation lemma `anmComposeBilin_mk`.
* **`anmCompose`** — the composition out of the (base-field) tensor product
  `A_{p,n}(𝒱) ⊗[ℂ] A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)` (`TensorProduct.lift anmComposeBilin`), with
  `anmCompose_tmul`.
* **`AnmComposeBalanced`** — the precise `A_n(𝒱)`-balancing `Prop` making the composition factor
  through `⊗_{A_n(𝒱)}` (DJ Prop 3.4): `(u *^{p,n} a) *^{p,n,m} v ≡ u *^{p,n,m} (a *^n_m v)` mod
  `O_{p,m}`, the equality `anmComposeBilin [u *^p_n a] [v] = anmComposeBilin [u] [a *^n_m v]`.
* `anmCompose_balanced_of_AnmComposeBalanced` — the bridge consuming `AnmComposeBalanced` to give the
  balancing on the descended map (the input a `TensorProduct ⊗_{A_n}` quotient consumes).

## What is OPEN (precise, NOT faked — see file end)

* The two descent `Prop`s `AnmComposeDescL`/`AnmComposeDescR` and the balancing `AnmComposeBalanced`
  are the genuine DJ Prop 3.4 residue-membership content (the level-mixing / depth-`p` analogues of
  the proven `m = 0` diagonal closure `AnmRightModule_closed`).  They are stated as precise `Prop`s,
  reduced to their generator families, and carried as explicit hypotheses — NOT axioms, NOT `sorry`.
* The genuine **`A_n(𝒱)` ring** (associativity/unit, `AnFull.AssocLaw`) is still upstream; until
  `A_n(𝒱)` is a Mathlib `Ring`, the literal Mathlib `TensorProduct (A_n(𝒱))` cannot be formed, so the
  composition is built out of the base-field `⊗[ℂ]` (the universal cover) and the `A_n`-balancing is
  carried as the explicit `Prop` `AnmComposeBalanced` (the quotient relation), exactly as `M(U)` is
  built over `⊗[ℂ]` in `ZhuVermaAnArchMU`.

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemma 2.8), §3 (Prop. 3.4), §4
(Thm 4.13); Dong–Li–Mason, J. Algebra 206 (1998) 67–96; H. Li `hep-th/9406211`; Gannon §5.3.2,
Thm 5.3.4.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators TensorProduct

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The Dong–Jiang composition product on `𝒱`. -/

/-- **The Dong–Jiang composition product** `u *^{p,n,m} v` for the bimodule composition
`A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱) → A_{p,m}(𝒱)` (DJ §3, Prop. 3.4).  It is the `A_{p,m}(𝒱)`
right-action residue formula `anmRight W p m u v` (shift `s = m`, binomial `p+i`, pole `p+i+1`):
the left factor's source level pair is `(p, n)`, the target is `(p, m)`, and `n` is the level over
which the two factors are balanced (it does not enter the residue formula). -/
noncomputable def anmCompose (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u v : 𝒱) : 𝒱 :=
  anmRight W p m u v

/-- The composition product is, by definition, the `A_{p,m}(𝒱)` right action `anmRight W p m`. -/
theorem anmCompose_eq_anmRight (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u v : 𝒱) :
    anmCompose W p n m u v = anmRight W p m u v := rfl

/-! ## ℂ-bilinearity of the composition product. -/

theorem anmCompose_add_left (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u₁ u₂ v : 𝒱) :
    anmCompose W p n m (u₁ + u₂) v = anmCompose W p n m u₁ v + anmCompose W p n m u₂ v :=
  anmRight_add_left W p m u₁ u₂ v

theorem anmCompose_smul_left (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmCompose W p n m (c • u) v = c • anmCompose W p n m u v :=
  anmRight_smul_left W p m c u v

theorem anmCompose_add_right (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u v₁ v₂ : 𝒱) :
    anmCompose W p n m u (v₁ + v₂) = anmCompose W p n m u v₁ + anmCompose W p n m u v₂ :=
  anmRight_add_right W p m u v₁ v₂

theorem anmCompose_smul_right (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmCompose W p n m u (c • v) = c • anmCompose W p n m u v :=
  anmRight_smul_right W p m c u v

@[simp] theorem anmCompose_zero_left (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (v : 𝒱) :
    anmCompose W p n m (0 : 𝒱) v = 0 := by
  have h := anmCompose_smul_left W p n m (0 : ℂ) (0 : 𝒱) v
  rwa [zero_smul, zero_smul] at h

@[simp] theorem anmCompose_zero_right (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u : 𝒱) :
    anmCompose W p n m u (0 : 𝒱) = 0 := by
  have h := anmCompose_smul_right W p n m (0 : ℂ) u (0 : 𝒱)
  rwa [zero_smul, zero_smul] at h

/-! ## The diagonal and bottom anchors (DJ Prop. 4.6 `A_{n,n} = A_n`; the Zhu bottom). -/

/-- At the diagonal `m = n = p` the composition is the `A_n(𝒱)` right action `anmRight W n n`
(consistent with DJ Prop. 4.6 `A_{n,n}(𝒱) = A_n(𝒱)`). -/
theorem anmCompose_diag_eq_anmRight (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v : 𝒱) :
    anmCompose W n n n u v = anmRight W n n u v := rfl

/-- At the bottom `(p,n,m) = (0,0,0)` the composition is Zhu's product `u * v` (`anmRight W 0 0`). -/
theorem anmCompose_zero_zero_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    anmCompose W 0 0 0 u v = zhuMul W u v := anmRight_zero_zero W u v

/-! ## The two single-slot ℂ-linear maps. -/

/-- The composition with a fixed right factor `v`, as a ℂ-linear map in the left factor
`u ↦ u *^{p,n,m} v` (the `A_{p,n}`-side). -/
noncomputable def anmComposeL (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (v : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u := anmCompose W p n m u v
  map_add' u₁ u₂ := anmCompose_add_left W p n m u₁ u₂ v
  map_smul' c u := anmCompose_smul_left W p n m c u v

@[simp] theorem anmComposeL_apply (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (v u : 𝒱) :
    anmComposeL W p n m v u = anmCompose W p n m u v := rfl

/-- The composition with a fixed left factor `u`, as a ℂ-linear map in the right factor
`v ↦ u *^{p,n,m} v` (the `A_{n,m}`-side). -/
noncomputable def anmComposeR (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun v := anmCompose W p n m u v
  map_add' v₁ v₂ := anmCompose_add_right W p n m u v₁ v₂
  map_smul' c v := anmCompose_smul_right W p n m c u v

@[simp] theorem anmComposeR_apply (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) (u v : 𝒱) :
    anmComposeR W p n m u v = anmCompose W p n m u v := rfl

/-! ## The two precise descent `Prop`s (DJ Prop. 3.4 well-definedness). -/

/-- **DJ Prop. 3.4 left descent.**  The composition carries the **left** ideal `O_{p,n}(𝒱)` of the
left factor into the target `O_{p,m}(𝒱)`: `O_{p,n} *^{p,n,m} 𝒱 ⊆ O_{p,m}`.  This is the
well-definedness of the composition in its `A_{p,n}(𝒱)` argument. -/
def AnmComposeDescL (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) : Prop :=
  ∀ g ∈ Onm W p n, ∀ v : 𝒱, anmCompose W p n m g v ∈ Onm W p m

/-- **DJ Prop. 3.4 right descent.**  The composition carries the **right** ideal `O_{n,m}(𝒱)` of the
right factor into the target `O_{p,m}(𝒱)`: `𝒱 *^{p,n,m} O_{n,m} ⊆ O_{p,m}`.  This is the
well-definedness of the composition in its `A_{n,m}(𝒱)` argument. -/
def AnmComposeDescR (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ) : Prop :=
  ∀ u : 𝒱, ∀ g ∈ Onm W n m, anmCompose W p n m u g ∈ Onm W p m

/-! ## Reduction of the two descents to their generator families. -/

/-- The left descent `AnmComposeDescL` reduced to its two LEFT-generator families: since
`u ↦ u *^{p,n,m} v` is ℂ-linear (`anmComposeL`), it suffices that the composition of each
`O_{p,n}`-generator (`anmCirc W p n c d` and `anmLgen W p n c`) with every `v` lands in
`O_{p,m}`. -/
theorem AnmComposeDescL_of_gens (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hcirc : ∀ c d v : 𝒱, anmCompose W p n m (anmCirc W p n c d) v ∈ Onm W p m)
    (hL : ∀ c v : 𝒱, anmCompose W p n m (anmLgen W p n c) v ∈ Onm W p m) :
    AnmComposeDescL W p n m := by
  intro g hg v
  have hle : Onm W p n ≤ (Onm W p m).comap (anmComposeL W p n m v) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmComposeL_apply] using hcirc c d v
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmComposeL_apply] using hL c v
  have hx' : g ∈ (Onm W p m).comap (anmComposeL W p n m v) := hle hg
  rwa [Submodule.mem_comap, anmComposeL_apply] at hx'

/-- The right descent `AnmComposeDescR` reduced to its two RIGHT-generator families: since
`v ↦ u *^{p,n,m} v` is ℂ-linear (`anmComposeR`), it suffices that the composition of every `u` with
each `O_{n,m}`-generator (`anmCirc W n m c d` and `anmLgen W n m c`) lands in `O_{p,m}`. -/
theorem AnmComposeDescR_of_gens (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hcirc : ∀ u c d : 𝒱, anmCompose W p n m u (anmCirc W n m c d) ∈ Onm W p m)
    (hL : ∀ u c : 𝒱, anmCompose W p n m u (anmLgen W n m c) ∈ Onm W p m) :
    AnmComposeDescR W p n m := by
  intro u g hg
  have hle : Onm W n m ≤ (Onm W p m).comap (anmComposeR W p n m u) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmComposeR_apply] using hcirc u c d
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmComposeR_apply] using hL u c
  have hx' : g ∈ (Onm W p m).comap (anmComposeR W p n m u) := hle hg
  rwa [Submodule.mem_comap, anmComposeR_apply] at hx'

/-! ## The descended bilinear composition map `A_{p,n}(𝒱) →ₗ A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)`.

Conditional ONLY on the two descent `Prop`s, the composition product descends through the quotients
on both slots, yielding the genuine ℂ-bilinear composition map (DJ Prop. 3.4 well-definedness). -/

section Bilin

variable (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)

/-- For a fixed left representative `u`, the right-slot descent `[v] ↦ [u *^{p,n,m} v]` as
`A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)`.  Well-defined by the right descent `hR` (`𝒱 *^{p,n,m} O_{n,m} ⊆
O_{p,m}`): `anmComposeR W p n m u` maps `O_{n,m}` into `O_{p,m}`, so it descends via `mapQ`. -/
noncomputable def anmComposeAux (hR : AnmComposeDescR W p n m) (u : 𝒱) :
    Anm W n m →ₗ[ℂ] Anm W p m :=
  (Onm W n m).mapQ (Onm W p m) (anmComposeR W p n m u) (by
    intro g hg
    rw [Submodule.mem_comap, anmComposeR_apply]
    exact hR u g hg)

@[simp] theorem anmComposeAux_mk (hR : AnmComposeDescR W p n m) (u v : 𝒱) :
    anmComposeAux W p n m hR u (mkAnm W n m v) = mkAnm W p m (anmCompose W p n m u v) := rfl

/-- `u ↦ anmComposeAux u` bundled as a ℂ-linear map `𝒱 →ₗ (A_{n,m} →ₗ A_{p,m})` (linear in the left
representative `u`). -/
noncomputable def anmComposeHom (hR : AnmComposeDescR W p n m) :
    𝒱 →ₗ[ℂ] Anm W n m →ₗ[ℂ] Anm W p m where
  toFun := anmComposeAux W p n m hR
  map_add' u₁ u₂ := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun v => ?_
    simp only [LinearMap.add_apply]
    rw [show (Submodule.Quotient.mk v : Anm W n m) = mkAnm W n m v from rfl,
      anmComposeAux_mk, anmComposeAux_mk, anmComposeAux_mk, anmCompose_add_left, map_add]
  map_smul' c u := by
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun v => ?_
    simp only [LinearMap.smul_apply, RingHom.id_apply]
    rw [show (Submodule.Quotient.mk v : Anm W n m) = mkAnm W n m v from rfl,
      anmComposeAux_mk, anmComposeAux_mk, anmCompose_smul_left, map_smul]

@[simp] theorem anmComposeHom_apply (hR : AnmComposeDescR W p n m) (u v : 𝒱) :
    anmComposeHom W p n m hR u (mkAnm W n m v) = mkAnm W p m (anmCompose W p n m u v) := rfl

/-- **The descended ℂ-bilinear Dong–Jiang composition map** (DJ Prop. 3.4)
`A_{p,n}(𝒱) →ₗ A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)`, `[u] ↦ [v] ↦ [u *^{p,n,m} v]`.  The right (`A_{n,m}`) slot
is descended via `hR` (inside `anmComposeAux`); the left (`A_{p,n}`) slot is descended here through
`A_{p,n} = 𝒱/O_{p,n}` via the left descent `hL` (`O_{p,n} *^{p,n,m} 𝒱 ⊆ O_{p,m}`, so `O_{p,n} ≤
ker`). -/
noncomputable def anmComposeBilin (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m) :
    Anm W p n →ₗ[ℂ] Anm W n m →ₗ[ℂ] Anm W p m :=
  (Onm W p n).liftQ (anmComposeHom W p n m hR) (by
    intro g hg
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun y => ?_
    refine Submodule.Quotient.induction_on _ y fun v => ?_
    change anmComposeHom W p n m hR g (mkAnm W n m v)
      = (0 : Anm W n m →ₗ[ℂ] Anm W p m) (mkAnm W n m v)
    rw [anmComposeHom_apply, LinearMap.zero_apply, mkAnm, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hL g hg v)

/-- **Representative-evaluation lemma** for the descended composition:
`[u] ∘ [v] = [u *^{p,n,m} v]`. -/
@[simp] theorem anmComposeBilin_mk (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m)
    (u v : 𝒱) :
    anmComposeBilin W p n m hL hR (mkAnm W p n u) (mkAnm W n m v)
      = mkAnm W p m (anmCompose W p n m u v) := rfl

end Bilin

/-! ## The composition out of the base-field tensor product `A_{p,n}(𝒱) ⊗[ℂ] A_{n,m}(𝒱)`.

Because the genuine `A_n(𝒱)` ring (associativity/unit) is still upstream, the literal Mathlib
`TensorProduct (A_n(𝒱))` cannot yet be formed; following `ZhuVermaAnArchMU`, we realize the
composition out of the base-field `⊗[ℂ]` (the universal cover of `⊗_{A_n(𝒱)}`).  The `A_n(𝒱)`
balancing is the precise `Prop` `AnmComposeBalanced` below; once `A_n(𝒱)` is a `Ring`, this map
factors through the genuine `⊗_{A_n(𝒱)}` (the quotient of `⊗[ℂ]` by the balancing relations). -/

/-- **The Dong–Jiang composition out of the base-field tensor product**
`A_{p,n}(𝒱) ⊗[ℂ] A_{n,m}(𝒱) →ₗ A_{p,m}(𝒱)`, conditional on the two descent `Prop`s
(`TensorProduct.lift` of the bilinear `anmComposeBilin`).  This is the universal cover of the genuine
`A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱) → A_{p,m}(𝒱)` of DJ Prop. 3.4. -/
noncomputable def anmCompose_lift (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m) :
    (Anm W p n) ⊗[ℂ] (Anm W n m) →ₗ[ℂ] Anm W p m :=
  TensorProduct.lift (anmComposeBilin W p n m hL hR)

/-- `anmCompose_lift` on a pure tensor of representatives: `[u] ⊗ [v] ↦ [u *^{p,n,m} v]`. -/
@[simp] theorem anmCompose_lift_tmul (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m) (u v : 𝒱) :
    anmCompose_lift W p n m hL hR (mkAnm W p n u ⊗ₜ[ℂ] mkAnm W n m v)
      = mkAnm W p m (anmCompose W p n m u v) := by
  rw [anmCompose_lift, TensorProduct.lift.tmul, anmComposeBilin_mk]

/-! ## The `A_n(𝒱)`-balancing `Prop` (DJ Prop. 3.4 factoring through `⊗_{A_n(𝒱)}`).

The genuine composition lives on `⊗_{A_n(𝒱)}`, i.e. the cover `⊗[ℂ]` quotient by the balancing
relations `[u *^p_n a] ⊗ [v] = [u] ⊗ [a *^n_m v]` for `a` representing `A_n(𝒱)`.  We state the
balancing as the precise `Prop`: the descended bilinear map identifies the two sides.  The middle
level `n` enters here (and ONLY here): `u *^p_n a` is the right `A_n(𝒱)`-action of `A_{p,n}`
(`anmRight W p n u a`), and `a *^n_m v` is the left `A_n(𝒱)`-action of `A_{n,m}`
(`anmRight W n m a v`). -/

/-- **DJ Prop. 3.4 `A_n(𝒱)`-balancing.**  For all representatives `u, a, v`, the descended
composition is balanced over `A_n(𝒱)`:
`anmComposeBilin [u *^p_n a] [v] = anmComposeBilin [u] [a *^n_m v]`, i.e. (mod `O_{p,m}`)
`(u *^p_n a) *^{p,n,m} v ≡ u *^{p,n,m} (a *^n_m v)`.  This is exactly the condition for the
composition to factor through `A_{p,n}(𝒱) ⊗_{A_n(𝒱)} A_{n,m}(𝒱)`. -/
def AnmComposeBalanced (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m) : Prop :=
  ∀ u a v : 𝒱,
    anmComposeBilin W p n m hL hR (mkAnm W p n (anmRight W p n u a)) (mkAnm W n m v)
      = anmComposeBilin W p n m hL hR (mkAnm W p n u) (mkAnm W n m (anmRight W n m a v))

/-- The balancing, as a representative identity in `A_{p,m}(𝒱)`:
`[(u *^p_n a) *^{p,n,m} v] = [u *^{p,n,m} (a *^n_m v)]`.  This is the direct unfolding of
`AnmComposeBalanced` via `anmComposeBilin_mk`; it is the exact relation the `⊗_{A_n(𝒱)}` quotient
imposes once `A_n(𝒱)` is a ring. -/
theorem AnmComposeBalanced_repr (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m)
    (hbal : AnmComposeBalanced W p n m hL hR) (u a v : 𝒱) :
    mkAnm W p m (anmCompose W p n m (anmRight W p n u a) v)
      = mkAnm W p m (anmCompose W p n m u (anmRight W n m a v)) := by
  have := hbal u a v
  rwa [anmComposeBilin_mk, anmComposeBilin_mk] at this

/-- The balancing reduced to its representative form: supplying the representative identity
`[(u *^p_n a) *^{p,n,m} v] = [u *^{p,n,m} (a *^n_m v)]` for all `u, a, v` discharges
`AnmComposeBalanced`.  (The clean bridge between the residue identity and the bilinear-map balancing
predicate.) -/
theorem AnmComposeBalanced_of_repr (W : VertexOperatorAlgebra 𝒱) (p n m : ℕ)
    (hL : AnmComposeDescL W p n m) (hR : AnmComposeDescR W p n m)
    (hrepr : ∀ u a v : 𝒱,
      mkAnm W p m (anmCompose W p n m (anmRight W p n u a) v)
        = mkAnm W p m (anmCompose W p n m u (anmRight W n m a v))) :
    AnmComposeBalanced W p n m hL hR := by
  intro u a v
  rw [anmComposeBilin_mk, anmComposeBilin_mk]
  exact hrepr u a v

/-! ## The `m = 0`, diagonal `p = n` specialization — bridging to the proven `AnmRightModule_closed`.

At `p = n` and `m = 0` the composition `anmCompose W n n 0 = anmRight W n 0` is exactly the proven
`m = 0` right `A_0(𝒱)`-action, whose descent is `AnmRightModule_closed` (the right slot at
level `(n,0)` over the base `O_{0,0}`).  We record the bridge: the right-slot generator families of
the `(p,n,m) = (n,0,0)` composition are exactly the already-closed `AnmCrossClosure` families. -/

/-- At `(p,n,m) = (n,0,0)` the composition product is the proven `m = 0` right action
`anmRight W n 0` (`anmCompose W n 0 0 = anmRight W n 0`).  This is the bottom-row case of the
composition (right factor in `A_{0,0}(𝒱) = A(𝒱)`, result in `A_{n,0}(𝒱)`), tying the composition to
the proven `AnmRightModule_closed` / `AnmCrossClosure` layer. -/
theorem anmCompose_n_zero_zero_eq (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v : 𝒱) :
    anmCompose W n 0 0 u v = anmRight W n 0 u v := rfl

/-! ## The precise OPEN Dong–Jiang Prop. 3.4 targets (NOT faked).

The composition map `anmComposeBilin` / `anmCompose_lift` is fully built and ℂ-bilinear, conditional
ONLY on the two descent `Prop`s `AnmComposeDescL`/`AnmComposeDescR`; the `A_n(𝒱)`-balancing is the
precise `Prop` `AnmComposeBalanced`.  The remaining DJ Prop. 3.4 residue-membership content is:

* `AnmComposeDescL W p n m` (`O_{p,n} *^{p,n,m} 𝒱 ⊆ O_{p,m}`), reduced to its two generator families
  (`AnmComposeDescL_of_gens`).  At the diagonal-bottom `(p,n,m) = (n,0,0)` this is exactly the proven
  `AnmRightModule W n` (`AnmRightModule_closed`), so the bottom row is closed; the general level-pair
  `(p,n,m)` is the level-mixing / depth-`p` analogue (the `O''_{p,m}`/`O'''_{p,m}` content of the full
  `O_{p,m}`, the analogue of `Pres_mem_On`).
* `AnmComposeDescR W p n m` (`𝒱 *^{p,n,m} O_{n,m} ⊆ O_{p,m}`), reduced to its two generator families
  (`AnmComposeDescR_of_gens`).  At `(p,n,m) = (n,0,0)` this is the proven `AnmCrossClosure W n`.
* `AnmComposeBalanced W p n m hL hR` (the `A_n(𝒱)`-balancing
  `(u *^p_n a) *^{p,n,m} v ≡ u *^{p,n,m} (a *^n_m v)` mod `O_{p,m}`), reduced to its representative
  form (`AnmComposeBalanced_of_repr`).  This is the associativity-of-composition core of DJ Prop. 3.4
  (the depth-`p` FZ associator combinatorics, the analogue of `AnFull.AssocLaw`).

All three are engine-verified TRUE (`n = 1`, free boson, `certificates/mathematica/`); none is an axiom or
`sorry`.  The composition map is genuinely built and ℂ-bilinear — only the residue-membership
hypotheses (the deep DJ Prop. 3.4 content) are carried as explicit `Prop`s, exactly as the upstream
`A_n(𝒱)` ring is carried in `ZhuVermaAnArchAlgebra`/`ZhuVermaAnArchMU`. -/

end VOA
