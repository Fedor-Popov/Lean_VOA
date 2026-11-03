/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchAlgebra

/-!
# The Dong–Jiang `A_{n,m}(𝒱)` bimodule foundation — toward `M(U)`

Building on the corrected `A_n(𝒱)` architecture (`ZhuVermaAnArch`/`ZhuVermaAnArchAlgebra`) and the
generic Frenkel–Zhu residue `resHom` (`ZhuVermaAnBimodule`), this file lays the **Dong–Jiang
bimodule** foundation (Dong–Jiang, *Bimodules associated to vertex operator algebras*, Math. Z. 259
(2008) 799–826, `math/0601626`). For each pair of levels `(n, m)` the construction produces an
`A_n(𝒱)`–`A_m(𝒱)` bimodule `A_{n,m}(𝒱) = 𝒱 / O_{n,m}(𝒱)`; the induced module of Zhu Thm 5.3.4 is
`M(U) = ⊕ₙ A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U`.

## The Dong–Jiang formulas (DJ §2, engine-verified on the rank-1 free boson, `certificates/mathematica/heis_engine.wl`)

For homogeneous `u ∈ 𝒱ₖ`:

* **Right `A_m`-action** `u *^n_m v = ∑ᵢ (-1)^i C(n+i,i) Res_z (1+z)^{k+m}/z^{n+i+1} Y(u,z)v`
* **Circle generator** `u ∘^n_m v = Res_z (1+z)^{k+m}/z^{n+m+2} Y(u,z)v`.
* **Grading generator** `(L₋₁ u + (L₀ + m − n) u)` (the SHIFTED relation, `+m−n`, NOT `L₋₁+L₀`).

All three are expressed through the existing generic residue `resHom W s p` (`= ∑ᵢ C(k+s,i)
u₍ᵢ₋ₚ₎ v = Res_z (1+z)^{k+s}/z^{p} Y(u,z)v`), with `s = m` and the appropriate pole `p`:
`u *^n_m v = ∑ᵢ (-1)ⁱ C(n+i,i) • resHom W m (n+i+1) u v`, `u ∘^n_m v = resHom W m (n+m+2) u v`.

## The `m = 0` specialization (the case `M(U)` needs)

At `m = 0` the right action collapses to a single `i = 0` term, and everything is a `resHom` with
shift `0`:

* `u *^n_0 v = resHom W 0 (n+1) u v` (`anmRight_zero`).
* `u ∘^n_0 v = resHom W 0 (n+2) u v` (`anmCirc_zero`).
* grading generator `L₋₁ u + (L₀ − n) u` (`anmLgen` at `m = 0`).

Engine-checks (`certificates/mathematica/heis_engine.wl`, free boson):
`u *^0_0 v = resHom 0 1 = zhuMul` (Zhu product); `u ∘^0_0 v = resHom 0 2 = circ_0` (Zhu's `O`
generator); both confirmed numerically. The crucial Dong–Jiang **Lemma 2.8** closures at
`(m,p) = (0,0)` — `O_{n,0} *^n_0 𝒱 ⊆ O_{n,0}` and `𝒱 *^n_0 O_{0,0} ⊆ O_{n,0}` — are
engine-verified TRUE (n = 1), which is exactly the well-definedness of the `V`-action on `M(U)`.

## What is proved here (axiom-clean)

* `anmRight W n m`, `anmCirc W n m`, `anmLgen W n m` — the three Dong–Jiang ingredients, all
  ℂ-bilinear (`anmRight_add_left/smul_left/add_right/smul_right`, ditto `anmCirc`).
* `anmRight_zero`/`anmCirc_zero` — the `m = 0` single-term reductions to `resHom`.
* `anmRight_zero_zero`/`anmCirc_zero_zero` — the `(n,m) = (0,0)` Zhu anchors
  (`= zhuMul`, `= resHom 0 2`).
* `OnmL W n m` (grading-generator span), `Onm W n m` (the `O'_{n,m}` part:
  `span{u ∘^n_m v} ⊔ OnmL`), `Anm W n m := 𝒱 ⧸ Onm W n m`, `mkAnm`, and the generator memberships
  `anmCirc_mem_Onm`, `anmLgen_mem_Onm`.
* `anmRightR W n m a` — `x ↦ a *^n_m x` as a ℂ-linear map (for the `span_le`/`comap` reductions).
* The reduction principle `anm_right_closure_of_gens` (DJ Lemma 2.8 reduced to its two generator
  families), and the `m = 0` packaged target `AnmRightModule W n` (the M(U) well-definedness Prop).

## What is OPEN (precise, NOT faked — see file end)

* The `O''_{n,m}` (associator-defect) and `O'''_{n,m}` (level-mixing) summands of the FULL
  `O_{n,m} = O'_{n,m} + O''_{n,m} + O'''_{n,m}` are NOT yet added (the `m = 0` `M(U)` closure is
  engine-true already on the `O'_{n,m}` part for the free boson; the full bimodule needs all three).
* The actual closures `AnmRightModule`/the cross closure `𝒱 *^n_0 O_0 ⊆ O_{n,0}` — engine-verified
  TRUE — are stated as precise `Prop`s reduced to their generator families, NOT proved here (they
  need the depth-`n` FZ residue-membership combinatorics, the analogue of `Pres_mem_On`).

## References
Dong–Jiang, Math. Z. 259 (2008) 799–826 (`math/0601626`), §2 (Lemmas 2.6, 2.8, Thm 2.9), §3
(Prop. 3.4); Dong–Li–Mason, J. Algebra 206 (1998) 67–96; H. Li, `hep-th/9406211`; Gannon §5.3.2.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## The three Dong–Jiang ingredients via the generic residue `resHom`. -/

/-- **Dong–Jiang right `A_m`-action** `u *^n_m v`
`= ∑_{i=0}^{m} (-1)^i C(n+i,i) · Res_z (1+z)^{wt u + m}/z^{n+i+1} Y(u,z)v`, expressed through the
generic FZ residue `resHom W m (n+i+1)` (shift `s = m`, pole `p = n+i+1`). At `m = 0` only the
`i = 0` term survives: `u *^n_0 v = resHom W 0 (n+1) u v` (`anmRight_zero`). -/
noncomputable def anmRight (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) : 𝒱 :=
  ∑ i ∈ Finset.range (m + 1),
    ((-1 : ℂ) ^ i * cbz ((n : ℤ) + i) (i : ℤ)) • resHom W (m : ℤ) ((n : ℤ) + (i : ℤ) + 1) u v

/-- **Dong–Jiang circle generator** `u ∘^n_m v = Res_z (1+z)^{wt u + m}/z^{2n+... }`; precisely
`Res_z (1+z)^{wt u + m}/z^{n+m+2} Y(u,z)v = resHom W m (n+m+2) u v` (shift `s = m`, pole `n+m+2`).
At `m = 0` it is `resHom W 0 (n+2) u v`; at `(n,m)=(0,0)` it is Zhu's `O`-gen `resHom W 0 2`. -/
noncomputable def anmCirc (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) : 𝒱 :=
  resHom W (m : ℤ) ((n : ℤ) + (m : ℤ) + 2) u v

/-- **Dong–Jiang grading generator** `L₋₁ u + (L₀ + m − n) u` (the SHIFTED relation `+m−n`, NOT
`L₋₁+L₀`; Dong–Jiang `O'_{n,m}`). At `m = 0` it is `L₋₁ u + (L₀ − n) u`; at `m = n` it is the
diagonal `L₋₁ u + L₀ u` (= the `A_n(𝒱)` relation `OnL`). -/
noncomputable def anmLgen (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u : 𝒱) : 𝒱 :=
  W.L (-1) u + W.L 0 u + ((m : ℂ) - (n : ℂ)) • u

/-! ## Bilinearity of the Dong–Jiang right action `*^n_m`. -/

theorem anmRight_add_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u₁ u₂ v : 𝒱) :
    anmRight W n m (u₁ + u₂) v = anmRight W n m u₁ v + anmRight W n m u₂ v := by
  simp only [anmRight, resHom_add_left, smul_add, Finset.sum_add_distrib]

theorem anmRight_smul_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmRight W n m (c • u) v = c • anmRight W n m u v := by
  simp only [anmRight, resHom_smul_left, Finset.smul_sum, smul_comm c]

theorem anmRight_add_right (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v₁ v₂ : 𝒱) :
    anmRight W n m u (v₁ + v₂) = anmRight W n m u v₁ + anmRight W n m u v₂ := by
  simp only [anmRight, resHom_add_right, smul_add, Finset.sum_add_distrib]

theorem anmRight_smul_right (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmRight W n m u (c • v) = c • anmRight W n m u v := by
  simp only [anmRight, resHom_smul_right, Finset.smul_sum, smul_comm c]

/-! ## Bilinearity of the Dong–Jiang circle generator `∘^n_m`. -/

theorem anmCirc_add_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u₁ u₂ v : 𝒱) :
    anmCirc W n m (u₁ + u₂) v = anmCirc W n m u₁ v + anmCirc W n m u₂ v := by
  simp only [anmCirc, resHom_add_left]

theorem anmCirc_smul_left (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmCirc W n m (c • u) v = c • anmCirc W n m u v := by
  simp only [anmCirc, resHom_smul_left]

theorem anmCirc_add_right (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v₁ v₂ : 𝒱) :
    anmCirc W n m u (v₁ + v₂) = anmCirc W n m u v₁ + anmCirc W n m u v₂ := by
  simp only [anmCirc, resHom_add_right]

theorem anmCirc_smul_right (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : ℂ) (u v : 𝒱) :
    anmCirc W n m u (c • v) = c • anmCirc W n m u v := by
  simp only [anmCirc, resHom_smul_right]

/-! ## Linearity of the grading generator `anmLgen`. -/

theorem anmLgen_add (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u₁ u₂ : 𝒱) :
    anmLgen W n m (u₁ + u₂) = anmLgen W n m u₁ + anmLgen W n m u₂ := by
  simp only [anmLgen, map_add, smul_add]; abel

theorem anmLgen_smul (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (c : ℂ) (u : 𝒱) :
    anmLgen W n m (c • u) = c • anmLgen W n m u := by
  simp only [anmLgen, map_smul, smul_add, smul_comm ((m : ℂ) - (n : ℂ)) c]

/-! ## The `m = 0` single-term reductions (the case `M(U)` induces from). -/

/-- **`u *^n_0 v = resHom W 0 (n+1) u v`** — at `m = 0` the Dong–Jiang right action collapses to the
single `i = 0` term, the single-pole residue `Res_z (1+z)^{wt u}/z^{n+1} Y(u,z)v`. -/
theorem anmRight_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v : 𝒱) :
    anmRight W n 0 u v = resHom W 0 ((n : ℤ) + 1) u v := by
  rw [anmRight, Finset.range_one, Finset.sum_singleton]
  simp only [Nat.cast_zero, pow_zero, add_zero, cbz_zero, mul_one, one_smul]

/-- **`u ∘^n_0 v = resHom W 0 (n+2) u v`** — the `m = 0` circle generator (double-shifted pole). -/
theorem anmCirc_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u v : 𝒱) :
    anmCirc W n 0 u v = resHom W 0 ((n : ℤ) + 2) u v := by
  simp only [anmCirc, Nat.cast_zero, add_zero]

/-! ## The `(n,m) = (0,0)` Zhu anchors (non-negotiable). -/

/-- **`u *^0_0 v = zhuMul W u v`** — at the bottom of the tower the Dong–Jiang right action is
exactly Zhu's product (`resHom W 0 1 = zhuMul`). -/
theorem anmRight_zero_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    anmRight W 0 0 u v = zhuMul W u v := by
  rw [anmRight_zero, Nat.cast_zero, zero_add, resHom_zero_one]

/-- **`u ∘^0_0 v = resHom W 0 2 u v`** — the bottom circle generator is exactly Zhu's `O`-generator
`Res_z (1+z)^{wt u}/z^2 Y(u,z)v` (engine-confirmed `= circ_0 u v` on the free boson). -/
theorem anmCirc_zero_zero (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    anmCirc W 0 0 u v = resHom W 0 2 u v := by
  rw [anmCirc_zero]; norm_num

/-! ## The grading generator at the diagonal `m = n` and at `m = 0`. -/

/-- At the diagonal `m = n`, the Dong–Jiang grading generator is exactly the `A_n(𝒱)` relation
`L₋₁ u + L₀ u` (so `O_{n,n}` matches `OnL`; this is Dong–Jiang Prop. 4.6 `A_{n,n} = A_n`). -/
theorem anmLgen_diag (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (u : 𝒱) :
    anmLgen W n n u = W.L (-1) u + W.L 0 u := by
  simp only [anmLgen, sub_self, zero_smul, add_zero]

/-! ## The `O'_{n,m}(𝒱)` part and the bimodule quotient `A_{n,m}(𝒱)`.

We build the `O'_{n,m}` part of `O_{n,m}` — the circle-generator span plus the shifted grading
generators.  (The full Dong–Jiang `O_{n,m} = O'_{n,m} + O''_{n,m} + O'''_{n,m}` also adds the
associator-defect `O''` and the level-mixing `O'''` summands; those are stated as the precise open
targets at the file end.  For the `m = 0`, `M(U)`-relevant closure, the `O'_{n,0}` part already
carries the engine-verified Lemma 2.8 closure on the free boson.) -/

/-- **`OnmL W n m`** — the span of the Dong–Jiang grading generators `L₋₁ u + (L₀ + m − n) u`. -/
def OnmL (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u : 𝒱, x = anmLgen W n m u}

/-- **`Onm W n m`** — the `O'_{n,m}(𝒱)` part: `span{u ∘^n_m v} ⊔ OnmL`. (The full `O_{n,m}` adds
`O''_{n,m} + O'''_{n,m}`; see the open targets below.) -/
def Onm (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x | ∃ u v : 𝒱, x = anmCirc W n m u v} ⊔ OnmL W n m

/-- **`A_{n,m}(𝒱) := 𝒱 / O'_{n,m}(𝒱)`** — the (partial) Dong–Jiang bimodule carrier. -/
abbrev Anm (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : Type u := 𝒱 ⧸ Onm W n m

/-- The quotient map `𝒱 →ₗ A_{n,m}(𝒱)`. -/
def mkAnm (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) : 𝒱 →ₗ[ℂ] Anm W n m := (Onm W n m).mkQ

/-- Circle generators land in `O'_{n,m}`. -/
theorem anmCirc_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) :
    anmCirc W n m u v ∈ Onm W n m :=
  le_sup_left (a := Submodule.span ℂ _) (b := OnmL W n m) (Submodule.subset_span ⟨u, v, rfl⟩)

/-- Grading generators land in `O'_{n,m}`. -/
theorem anmLgen_mem_Onm (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u : 𝒱) :
    anmLgen W n m u ∈ Onm W n m :=
  le_sup_right (a := Submodule.span ℂ _) (b := OnmL W n m) (Submodule.subset_span ⟨u, rfl⟩)

/-- `[u ∘^n_m v] = 0` in `A_{n,m}(𝒱)`. -/
@[simp] theorem mkAnm_anmCirc (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u v : 𝒱) :
    mkAnm W n m (anmCirc W n m u v) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (anmCirc_mem_Onm W n m u v)

/-- `[L₋₁ u + (L₀ + m − n) u] = 0` in `A_{n,m}(𝒱)`. -/
@[simp] theorem mkAnm_anmLgen (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u : 𝒱) :
    mkAnm W n m (anmLgen W n m u) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (anmLgen_mem_Onm W n m u)

/-! ## The `m = 0` identification with the `A_n(𝒱)` quotient generators.

At `m = 0` the Dong–Jiang `O'_{n,0}` circle generator is `resHom W 0 (n+2)`, and the
Dong–Jiang grading generator is `L₋₁ u + (L₀ − n) u`.  These tie `A_{n,0}` to the existing
`A_n(𝒱) = 𝒱/OnFull` machinery (`OnFull = span{circ} ⊔ OnL`) at the bottom level `n = 0`, where
`O'_{0,0} = O(𝒱)` exactly (`anmCirc_zero_zero`, `anmLgen_diag` at `n = m = 0`). -/

/-- At `(n,m) = (0,0)` the Dong–Jiang grading generator is Zhu's `(L₋₁ + L₀)u`. -/
theorem anmLgen_zero_zero (W : VertexOperatorAlgebra 𝒱) (u : 𝒱) :
    anmLgen W 0 0 u = W.L (-1) u + W.L 0 u := anmLgen_diag W 0 u

/-! ## Linear-map wrapper for the right action and the Dong–Jiang Lemma 2.8 reduction. -/

/-- Right `A_m`-action `x ↦ u *^n_m x` as a ℂ-linear map (the `M(U)` cross-action; for the
`span_le`/`comap` reductions of DJ Lemma 2.8). -/
noncomputable def anmRightR (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun x := anmRight W n m u x
  map_add' := anmRight_add_right W n m u
  map_smul' c x := anmRight_smul_right W n m c u x

@[simp] theorem anmRightR_apply (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u x : 𝒱) :
    anmRightR W n m u x = anmRight W n m u x := rfl

/-- Right action `u ↦ u *^n_m x` as a ℂ-linear map in the LEFT factor (`A_{n,m}`-side). -/
noncomputable def anmRightL (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (x : 𝒱) : 𝒱 →ₗ[ℂ] 𝒱 where
  toFun u := anmRight W n m u x
  map_add' u₁ u₂ := anmRight_add_left W n m u₁ u₂ x
  map_smul' c u := anmRight_smul_left W n m c u x

@[simp] theorem anmRightL_apply (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (x u : 𝒱) :
    anmRightL W n m x u = anmRight W n m u x := rfl

/-- `O'_{n,m}(𝒱)` as a span (definitional unfold for `span_le`). -/
theorem Onm_eq_sup_span (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) :
    Onm W n m
      = Submodule.span ℂ {x | ∃ u v : 𝒱, x = anmCirc W n m u v} ⊔ OnmL W n m := rfl

/-- **Right-slot reduction (DJ Lemma 2.8, `O'` part).**  If `u *^n_m (·)` maps every
`O'_{n,m}`-generator (circle generator and grading generator) into `O'_{n,m}`, then it maps all of
`O'_{n,m}` into `O'_{n,m}` (the action `x ↦ u *^n_m x` is ℂ-linear, so `comap`/`span_le`).  This is
the `M(U)` well-definedness reduction: the action of `u` on `A_{n,m}(𝒱)` is well defined precisely
when this holds. -/
theorem anm_right_closure_of_gens (W : VertexOperatorAlgebra 𝒱) (n m : ℕ) (u : 𝒱)
    (hcirc : ∀ c d : 𝒱, anmRight W n m u (anmCirc W n m c d) ∈ Onm W n m)
    (hL : ∀ c : 𝒱, anmRight W n m u (anmLgen W n m c) ∈ Onm W n m) :
    ∀ x ∈ Onm W n m, anmRight W n m u x ∈ Onm W n m := by
  have hle : Onm W n m ≤ (Onm W n m).comap (anmRightR W n m u) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro g ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightR_apply] using hcirc c d
    · rw [OnmL, Submodule.span_le]
      rintro g ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightR_apply] using hL c
  intro x hx
  have hx' : x ∈ (Onm W n m).comap (anmRightR W n m u) := hle hx
  rwa [Submodule.mem_comap, anmRightR_apply] at hx'

/-! ## The precise OPEN Dong–Jiang Lemma 2.8 targets (the `M(U)` well-definedness, NOT faked).

The `V`-action on `M(U) = ⊕ₙ A_{n,m}(𝒱) ⊗_{A_m(𝒱)} U` is well defined precisely when the
Dong–Jiang closures (Lemma 2.8, `math/0601626`) hold.  We state them as `Prop`s on the `O'_{n,m}`
part for the `m = 0` case `M(U)` induces from (engine-verified TRUE for `n = 1` on the rank-1 free
boson, `certificates/mathematica/heis_engine.wl`): they are NOT axioms and NOT `sorry`'d — they are the precise remaining
identities, reduced (via `anm_right_closure_of_gens`) to their two generator families. -/

/-- **DJ Lemma 2.8 right-module closure (the `M(U)` diagonal target, `m = 0`).**
`O'_{n,0}(𝒱) *^n_0 𝒱 ⊆ O'_{n,0}(𝒱)`: the right `A_0`-action descends to `A_{n,0}(𝒱)` (so
`A_{n,0}(𝒱)` is a right `A_0(𝒱) = A(𝒱)`-module).  Engine-verified TRUE (`n = 1`, free boson). -/
def AnmRightModule (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ g ∈ Onm W n 0, ∀ v : 𝒱, anmRight W n 0 g v ∈ Onm W n 0

/-- **DJ Lemma 2.8 cross closure (the `M(U)` `V`-action target, `m = p = 0`).**
`𝒱 *^n_0 O_{0,0}(𝒱) ⊆ O'_{n,0}(𝒱)` where `O_{0,0} = O(𝒱) = O'_{0,0}` (`Onm W 0 0`): the action of
`v ∈ 𝒱` carries the level-`0` relations into the level-`n` relations.  This is exactly the
well-definedness instance of `u_p` on `M(U)` (DJ lines 2087–2092).  Engine-verified TRUE
(`n = 1`, free boson). -/
def AnmCrossClosure (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Prop :=
  ∀ a : 𝒱, ∀ g ∈ Onm W 0 0, anmRight W n 0 a g ∈ Onm W n 0

/-- The `M(U)` right-module closure `O'_{n,0} *^n_0 𝒱 ⊆ O'_{n,0}`, reduced to its two
LEFT-generator families.  Since `anmRight (·) v` is ℂ-linear in the left factor (`anmRightL`), it
suffices that the right action of each `O'_{n,0}`-generator (`anmCirc c d` and `anmLgen c`) lands in
`O'_{n,0}`, for every right factor `v`.  This isolates the genuine remaining FZ residue-membership
content (the depth-`n` analogue of `Pres_mem_On`) to the two generator families. -/
theorem AnmRightModule_of_gens (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcirc : ∀ c d v : 𝒱, anmRight W n 0 (anmCirc W n 0 c d) v ∈ Onm W n 0)
    (hL : ∀ c v : 𝒱, anmRight W n 0 (anmLgen W n 0 c) v ∈ Onm W n 0) :
    AnmRightModule W n := by
  intro g hg v
  have hle : Onm W n 0 ≤ (Onm W n 0).comap (anmRightL W n 0 v) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightL_apply] using hcirc c d v
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightL_apply] using hL c v
  have hx' : g ∈ (Onm W n 0).comap (anmRightL W n 0 v) := hle hg
  rwa [Submodule.mem_comap, anmRightL_apply] at hx'

/-- The `M(U)` cross closure `𝒱 *^n_0 O_{0,0} ⊆ O'_{n,0}`, reduced to its two RIGHT-generator
families (the level-`0` `O_{0,0} = O'_{0,0}` generators `anmCirc W 0 0 c d` and `anmLgen W 0 0 c`).
Since `anmRight a (·)` is ℂ-linear in the right factor (`anmRightR`), it suffices that the action of
each `a ∈ 𝒱` on each level-`0` generator lands in `O'_{n,0}`. -/
theorem AnmCrossClosure_of_gens (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcirc : ∀ a c d : 𝒱, anmRight W n 0 a (anmCirc W 0 0 c d) ∈ Onm W n 0)
    (hL : ∀ a c : 𝒱, anmRight W n 0 a (anmLgen W 0 0 c) ∈ Onm W n 0) :
    AnmCrossClosure W n := by
  intro a g hg
  have hle : Onm W 0 0 ≤ (Onm W n 0).comap (anmRightR W n 0 a) := by
    rw [Onm_eq_sup_span]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨c, d, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightR_apply] using hcirc a c d
    · rw [OnmL, Submodule.span_le]
      rintro x ⟨c, rfl⟩
      simpa only [SetLike.mem_coe, Submodule.mem_comap, anmRightR_apply] using hL a c
  have hx' : g ∈ (Onm W n 0).comap (anmRightR W n 0 a) := hle hg
  rwa [Submodule.mem_comap, anmRightR_apply] at hx'

end VOA
