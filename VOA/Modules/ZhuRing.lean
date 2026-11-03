/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuModule

/-!
# The associative algebra `A(𝒱)` — instance engineering modulo Zhu Thm 2.1.1/2.1.2

The complete `Ring`/`Algebra`/`Module` stack for Zhu's algebra `A(𝒱)`, built **parametric in one
bundled, explicitly-stated hypothesis** `ZhuRingData W` (Gannon §5.3.2 / Zhu Thm 2.1.1–2.1.2:
`O(𝒱)` is a two-sided ideal for `*` and `*` is associative mod `O(𝒱)`):

* `zhuMulₗ` (the Zhu product as a `ℂ`-bilinear map), `descendBilinZ` (two-sided-ideal descent to
  `A(𝒱)`), `mk_surjective`/`mk_eq_iff`/`mk_eq_zero_iff`.
* **`structure ZhuRingData W`** — bundles the three crux facts; **`zhuRingData_of_gens`** reduces it
  to three explicit residue goals (left-ideal generator, right-ideal generator, associator).
* **`AsRing`/`AsAlgebra`** — the (noncommutative) ring and `ℂ`-algebra on `A(𝒱)` (reusing the
  quotient `AddCommGroup`, no diamond), and **`AsModule : Module (A 𝒱) M_h`** (`actA_mul`,
  `actARingHom`) — upgrading the Theorem 5.3.4 easy-direction action `ZhuModule.actA` to a genuine
  module — all the *instant* `ZhuRingData W` is supplied. Unit-factor special cases of the three
  goals are proved (`left_gen_b_vacuum`, `assoc_vacuum_*`, …).

## Status
`sorry`-free, with no project axioms.  The instance engineering, the bilinear descent,
the reduction `zhuRingData_of_gens`, and the unit-factor cases — all axiom-clean.

**`ZhuRingData W` is a THEOREM, not a hypothesis** — discharged unconditionally in
`Modules.ZhuRingInstance` as `zhuRingData_holds` (Zhu Thm 2.1.1–2.1.2), off the proved residue
cores `ZhuRightIdeal.right_ideal_core` (the linchpin `ZhuRingResidue.zhu_right_binom`) and
`ZhuAssociator.associator_core` (`u_core`/`v_core`/`mu_identity` + the `mode_iterate` two-family
bookkeeping), with the left ideal free from the associator (`ZhuRingResidue.left_ideal_gen_of_assoc`).
So `AsRing`/`AsAlgebra`/`AsModule` upgrade to the unconditional `instRingA : Ring (A 𝒱)`,
`instAlgebraA : Algebra ℂ (A 𝒱)`, `moduleMh : Module (A 𝒱) M_h` (`ZhuRingInstance`) — `VOA.pbw`
is not used.

## References
* Gannon §5.3.2, Thm 5.3.4; Zhu [574] Thm 2.1.1–2.1.2; Frenkel–Zhu.
-/

namespace VOA

open VertexOperatorAlgebra
open Module (End)
open scoped BigOperators
open Classical

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## Package the Zhu product as a `ℂ`-bilinear map. -/

/-- The Zhu product as a `ℂ`-bilinear map `𝒱 →ₗ 𝒱 →ₗ 𝒱`. -/
noncomputable def zhuMulₗ (W : VertexOperatorAlgebra 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u :=
    { toFun := fun v => zhuMul W u v
      map_add' := fun v₁ v₂ => zhuMul_add_right W u v₁ v₂
      map_smul' := fun c v => zhuMul_smul_right W c u v }
  map_add' u₁ u₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    exact zhuMul_add_left W u₁ u₂ v
  map_smul' c u := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
    exact zhuMul_smul_left W c u v

@[simp] theorem zhuMulₗ_apply (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    zhuMulₗ W u v = zhuMul W u v := rfl

/-! ## Quotient bookkeeping for `A W = 𝒱 ⧸ O W`. -/

theorem mk_surjective (W : VertexOperatorAlgebra 𝒱) : Function.Surjective (mk W) :=
  Submodule.mkQ_surjective _

theorem mk_eq_iff (W : VertexOperatorAlgebra 𝒱) {u v : 𝒱} :
    mk W u = mk W v ↔ u - v ∈ O W := by
  rw [mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

theorem mk_eq_zero_iff (W : VertexOperatorAlgebra 𝒱) {u : 𝒱} :
    mk W u = 0 ↔ u ∈ O W := by
  rw [mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-! ## Descend a two-sided-ideal bilinear map to `A W`.

Copies the `PoissonDescent.descendBilinZ` machinery (`O` not necessarily a symmetric ideal). -/

/-- Right-lift of `B`: `O W ≤ ker (B.compr₂ mk).flip`. -/
theorem descend_right_kerZ (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O W → B u v ∈ O W) :
    O W ≤ LinearMap.ker (B.compr₂ (mk W)).flip := by
  intro v hv
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.zero_apply, mk]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hright u hv)

/-- Left-lift of `B`. -/
theorem descend_left_kerZ (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ O W → ∀ v, B u v ∈ O W)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O W → B u v ∈ O W) :
    O W ≤ LinearMap.ker
      (((O W).liftQ (B.compr₂ (mk W)).flip (descend_right_kerZ W B hright)).flip) := by
  intro u hu
  rw [LinearMap.mem_ker]
  refine LinearMap.ext fun vb => ?_
  refine Submodule.Quotient.induction_on _ vb fun v => ?_
  simp only [LinearMap.flip_apply, Submodule.liftQ_apply, LinearMap.compr₂_apply,
    LinearMap.zero_apply, mk]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (hleft hu v)

/-- **Generic descent** of a `ℂ`-bilinear map `B : 𝒱 →ₗ 𝒱 →ₗ 𝒱` to `A W`, given `O` is a
two-sided ideal for `B`.  Returns `A W →ₗ A W →ₗ A W` with `descend B ū v̄ = mk (B u v)`. -/
noncomputable def descendBilinZ (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ O W → ∀ v, B u v ∈ O W)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O W → B u v ∈ O W) :
    A W →ₗ[ℂ] A W →ₗ[ℂ] A W :=
  (O W).liftQ
    (((O W).liftQ (B.compr₂ (mk W)).flip (descend_right_kerZ W B hright)).flip)
    (descend_left_kerZ W B hleft hright)

theorem descendBilinZ_apply (W : VertexOperatorAlgebra 𝒱) (B : 𝒱 →ₗ[ℂ] 𝒱 →ₗ[ℂ] 𝒱)
    (hleft : ∀ {u : 𝒱}, u ∈ O W → ∀ v, B u v ∈ O W)
    (hright : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O W → B u v ∈ O W) (u v : 𝒱) :
    descendBilinZ W B hleft hright (mk W u) (mk W v) = mk W (B u v) := by
  simp only [descendBilinZ, mk, Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.flip_apply,
    LinearMap.compr₂_apply]

/-! ## The crux data: `O` is a two-sided `*`-ideal and `*` is associative mod `O`.

Bundled as a structure so the `Ring`/`Algebra`/`Module` consumers below are *parametric* in the
crux (Zhu Thm 2.1.1/2.1.2).  Discharging `ZhuRingData W` yields all the algebra structure. -/

/-- The genuine analytic content of Zhu Thm 2.1.1/2.1.2: `O W` is a two-sided ideal for the Zhu
product, and the Zhu product is associative modulo `O W`. -/
structure ZhuRingData (W : VertexOperatorAlgebra 𝒱) : Prop where
  /-- `O` is a left ideal: `u ∈ O ⟹ u * v ∈ O`. -/
  left_ideal : ∀ {u : 𝒱}, u ∈ O W → ∀ v, zhuMul W u v ∈ O W
  /-- `O` is a right ideal: `v ∈ O ⟹ u * v ∈ O`. -/
  right_ideal : ∀ (u : 𝒱) {v : 𝒱}, v ∈ O W → zhuMul W u v ∈ O W
  /-- `*` is associative mod `O`: `(u*v)*w − u*(v*w) ∈ O`. -/
  assoc : ∀ u v w : 𝒱, zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W

section RingFromData
variable {W : VertexOperatorAlgebra 𝒱} (hZ : ZhuRingData W)

/-- The descended Zhu product `A W →ₗ A W →ₗ A W`, `[u]·[v] = [u*v]`. -/
noncomputable def Amul : A W →ₗ[ℂ] A W →ₗ[ℂ] A W :=
  descendBilinZ W (zhuMulₗ W)
    (fun {u} hu v => hZ.left_ideal hu v)
    (fun u {v} hv => hZ.right_ideal u hv)

@[simp] theorem Amul_mk (u v : 𝒱) :
    Amul hZ (mk W u) (mk W v) = mk W (zhuMul W u v) := by
  rw [Amul, descendBilinZ_apply]; rfl

/-- Associativity of the descended product on `A W`. -/
theorem Amul_assoc (p q r : A W) :
    Amul hZ (Amul hZ p q) r = Amul hZ p (Amul hZ q r) := by
  obtain ⟨u, rfl⟩ := mk_surjective W p
  obtain ⟨v, rfl⟩ := mk_surjective W q
  obtain ⟨w, rfl⟩ := mk_surjective W r
  rw [Amul_mk, Amul_mk, Amul_mk, Amul_mk, mk_eq_iff]
  exact hZ.assoc u v w

/-- Left unit `[𝟙]·[v] = [v]`. -/
theorem Amul_one_left (p : A W) : Amul hZ (mk W W.vacuum) p = p := by
  obtain ⟨v, rfl⟩ := mk_surjective W p
  rw [Amul_mk, zhuMul_vacuum_left]

/-- Right unit `[v]·[𝟙] = [v]`. -/
theorem Amul_one_right (p : A W) : Amul hZ p (mk W W.vacuum) = p := by
  obtain ⟨v, rfl⟩ := mk_surjective W p
  rw [Amul_mk, zhuMul_vacuum_right]

/-- **Zhu's algebra `A(W)` as a (noncommutative) `Ring`** (Zhu Thm 2.1.1/2.1.2), built on the
existing quotient `AddCommGroup` (no additive diamond): the multiplication is the descended Zhu
product `[u]·[v] = [u*v]`, the unit is `[𝟙]`. -/
@[reducible] noncomputable def AsRing : Ring (A W) :=
  { (inferInstance : AddCommGroup (A W)) with
    mul := fun p q => Amul hZ p q
    one := mk W W.vacuum
    mul_assoc := Amul_assoc hZ
    one_mul := Amul_one_left hZ
    mul_one := Amul_one_right hZ
    left_distrib := fun p q r => by
      show Amul hZ p (q + r) = Amul hZ p q + Amul hZ p r
      rw [map_add]
    right_distrib := fun p q r => by
      show Amul hZ (p + q) r = Amul hZ p r + Amul hZ q r
      rw [map_add]; rfl
    zero_mul := fun p => by
      show Amul hZ 0 p = 0
      rw [map_zero]; rfl
    mul_zero := fun p => by
      show Amul hZ p 0 = 0
      rw [map_zero] }

/-- Under `AsRing hZ`, the product is `Amul`. -/
theorem AsRing_mul_eq (p q : A W) : (letI := AsRing hZ; p * q) = Amul hZ p q := rfl

/-- **`A(W)` is a `ℂ`-algebra** (the `ℂ`-bilinearity of the Zhu product makes scalars central). -/
@[reducible] noncomputable def AsAlgebra : @Algebra ℂ (A W) _ (AsRing hZ).toSemiring :=
  letI := AsRing hZ
  @Algebra.ofModule ℂ (A W) _ (AsRing hZ).toSemiring (inferInstance : Module ℂ (A W))
    (fun c p q => by
      change Amul hZ (c • p) q = c • Amul hZ p q
      rw [map_smul]; rfl)
    (fun c p q => by
      change Amul hZ p (c • q) = c • Amul hZ p q
      rw [map_smul])

end RingFromData

/-! ## The `A(W)`-module structure on a lowest-weight space `M_h`.

With the `Ring (A W)` in hand, the descended action `actA` upgrades from a `ℂ`-linear map that is
multiplicative on representable products (`actA_mk_mul`) to a genuine `Module (A W) (N.weight h)`.
`ρ : A W →+* End ℂ M_h` is a ring hom (multiplicativity over all of `A W` follows by surjectivity
of `mk` and the representative-level `actA_mk_mul`). -/

section ModuleStructure
variable {Mod : Type u} [AddCommGroup Mod] [Module ℂ Mod] {W : VertexOperatorAlgebra 𝒱}
variable (hZ : ZhuRingData W) {N : OrdVModule W Mod} {h : ℂ} (hcw : IsLowestWeight N h)

/-- `actA` is multiplicative on **all** of `A W` (not just representable products): for `p q : A W`,
`actA (p * q) = actA p * actA q`.  By surjectivity of `mk` + `actA_mk_mul`. -/
theorem actA_mul (p q : A W) :
    actA N hcw (letI := AsRing hZ; p * q) = actA N hcw p * actA N hcw q := by
  obtain ⟨u, rfl⟩ := mk_surjective W p
  obtain ⟨v, rfl⟩ := mk_surjective W q
  rw [AsRing_mul_eq, Amul_mk, actA_mk_mul]

/-- The action `actA` packaged as a **ring homomorphism** `A W →+* End ℂ M_h`. -/
noncomputable def actARingHom : letI := AsRing hZ; (A W) →+* End ℂ (N.weight h) :=
  letI := AsRing hZ
  { toFun := fun p => actA N hcw p
    map_one' := by show actA N hcw (mk W W.vacuum) = 1; rw [← one]; exact actA_one N hcw
    map_mul' := fun p q => actA_mul hZ hcw p q
    map_zero' := by rw [map_zero]
    map_add' := fun p q => by rw [map_add] }

/-- **The `A(W)`-module structure on the lowest-weight space `M_h`** (Theorem 5.3.4, easy
direction, a genuine `Module` via the `Ring (A W)`): `[u] · x = o(u) x`.
The scalar tower over `ℂ` holds since both actions are `ℂ`-linear. -/
@[reducible] noncomputable def AsModule :
    letI := AsRing hZ; letI := AsAlgebra hZ; Module (A W) (N.weight h) :=
  letI := AsRing hZ
  letI := AsAlgebra hZ
  Module.compHom (N.weight h) (actARingHom hZ hcw)

end ModuleStructure

/-! ## Discharging `ZhuRingData` — the genuine Zhu Thm 2.1.1/2.1.2 crux.

We reduce the two ideal directions to per-generator conditions
(`left_ideal_of_gen`/`right_ideal_of_gen`).  The remaining goals are the genuine residue
identities. -/

section Crux
variable (W : VertexOperatorAlgebra 𝒱)

/-- Reduction: `ZhuRingData` follows from the per-generator ideal conditions and the
associator condition. -/
theorem zhuRingData_of_gens
    (hL : ∀ g ∈ Ogen W, ∀ v, zhuMul W g v ∈ O W)
    (hR : ∀ u, ∀ g ∈ Ogen W, zhuMul W u g ∈ O W)
    (hA : ∀ u v w : 𝒱, zhuMul W (zhuMul W u v) w - zhuMul W u (zhuMul W v w) ∈ O W) :
    ZhuRingData W where
  left_ideal := fun {u} hu v => left_ideal_of_gen W v (fun g hg => hL g hg v) u hu
  right_ideal := fun u {v} hv => right_ideal_of_gen W u (fun g hg => hR u g hg) v hv
  assoc := hA

/-! ### Genuine special-case discharges of the per-generator ideal conditions.

The unit (`𝟙`) cases of both ideal directions and of the spectator factor are unconditional
(off the unit laws `zhuMul_vacuum_left`/`right` and `gen_mem_O`). The general per-generator
conditions are the genuine Frenkel–Zhu residue frontier (see `### Remaining frontier`). -/

/-- **Left-ideal generator, `b = 𝟙`**: `((L₋₁a+L₀a)*𝟙) * v ∈ O`.  Here `(L₋₁a+L₀a)*𝟙 = L₋₁a+L₀a`
(`zhuMul_vacuum_right`), so the product is literally a generator of `O`. -/
theorem left_ideal_gen_vacuum (a v : 𝒱) :
    zhuMul W (zhuMul W (W.L (-1) a + W.L 0 a) W.vacuum) v ∈ O W := by
  rw [zhuMul_vacuum_right]; exact gen_mem_O W a v

/-- **Right-ideal generator, `u = 𝟙`**: `𝟙 * ((L₋₁a+L₀a)*b) ∈ O` (the generator is fixed by the
left unit). -/
theorem right_ideal_gen_vacuum (a b : 𝒱) :
    zhuMul W W.vacuum (zhuMul W (W.L (-1) a + W.L 0 a) b) ∈ O W := by
  rw [zhuMul_vacuum_left]; exact gen_mem_O W a b

/-- **Right-ideal generator, `b = 𝟙`**: `u * ((L₋₁a+L₀a)*𝟙) = u * (L₋₁a+L₀a)`.  Reduces the
`b = 𝟙` right-ideal case to the bare right-multiplication `u * (L₋₁a+L₀a) ∈ O`. -/
theorem right_ideal_gen_b_vacuum_eq (u a : 𝒱) :
    zhuMul W u (zhuMul W (W.L (-1) a + W.L 0 a) W.vacuum)
      = zhuMul W u (W.L (-1) a + W.L 0 a) := by
  rw [zhuMul_vacuum_right]

end Crux

/-!
### `ZhuRingData` discharged (Zhu Thm 2.1.1/2.1.2) — no `sorry`, no new `axiom`

`ZhuRingData W` is proved unconditionally (`Modules.ZhuRingInstance.zhuRingData_holds`) via
`zhuRingData_of_gens`, from the three residue facts (each homogeneous-reducible by bilinearity):

1. **Left-ideal generator** `((L₋₁a+L₀a)*b) * v ∈ O` — free from the associator
   (`ZhuRingResidue.left_ideal_gen_of_assoc`: `((L₋₁a+L₀a)*b)*v = (L₋₁a+L₀a)*(b*v) + [assoc] ∈ O`).
2. **Right-ideal generator** `u * ((L₋₁a+L₀a)*b) ∈ O` — `ZhuRightIdeal.right_ideal_core`: off
   `right_target_expand` + the `mode_commutator` split, the per-`j` term collapses into the proved
   `Pres` family by the linchpin `ZhuRingResidue.zhu_right_binom`
   (`S_j = ∑_{n=1}^{j+1} (-1)^{n-1} C(K,j-n+1) · Pres(u₍ⱼ₎a, K+M-j-1, b, n) ∈ O`).
3. **Associator** `(u*v)*w − u*(v*w) ∈ O` — `ZhuAssociator.associator_core`: the two-family
   `mode_iterate` decomposition `= Σ μ(L,b,n)·Pres(u,K,v₍ᵦ₎w,n) + Σ μ(K,a,n)·Pres(v,L,u₍ₐ₎w,n)`,
   off `ZhuUCore.u_core`/`ZhuVCore.v_core`/`ZhuMuIdentity.mu_identity`.

So `AsRing`/`AsAlgebra`/`AsModule` upgrade to the **unconditional** `instRingA : Ring (A 𝒱)`,
`instAlgebraA : Algebra ℂ (A 𝒱)`, `moduleMh : Module (A 𝒱) M_h` (`Modules.ZhuRingInstance`) —
all `[propext, Classical.choice, Quot.sound]`.  The unit-factor cases (`left_ideal_gen_vacuum`,
`right_ideal_gen_vacuum`, `zhuMul_assoc_vacuum_left/mid/right` in `ZhuModule`) are the easy slices.
-/

end VOA
