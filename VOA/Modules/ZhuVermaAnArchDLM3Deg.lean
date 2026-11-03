/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchMUVhat
import VOA.Core.Reconstruction

/-!
# DLM3 §3 — the degree calculus of `V̂` and the parabolic `P_n`

Dong–Li–Mason, *Vertex operator algebras and associative algebras*, J. Algebra **206** (1998)
67–96 (arXiv `q-alg/9612010v2`), §3, equations (3.1)–(3.3), builds the induced module of their
Theorem 4.1 out of three ingredients:

* the `ℤ`-graded Lie algebra `V̂ = ℂ[t,t⁻¹] ⊗ 𝒱 / D(ℂ[t,t⁻¹] ⊗ 𝒱)` with
  `deg (v(m)) = wt v − m − 1` and `[V̂(d), V̂(e)] ⊆ V̂(d+e)`;
* the **parabolic** `P_n = V̂(0) ⊕ ⨁_{p > n} V̂(−p)`, a Lie subalgebra of `V̂`;
* the trivial action of the *deep* part `⨁_{p > n} V̂(−p)` on an `A_n(𝒱)`-module.

The repo already owns the Lie algebra itself (`VHat.lieRing`/`VHat.lieAlgebra`,
`ZhuVermaAnArchVhatJac3` — the three Frenkel–Zhu obligations are proved theorems there, so the
project is *ahead* of DLM3 on its own §3) and the generator grading `VHat.deg`
(`ZhuVermaAnArchVhat`), but not the **grading of the bracket**.  This file supplies exactly that,
plus the objects DLM3 §4 needs on top of it:

* `VHat.degSpan W S` — the span of the generators `a(m)` whose degree `wt a − m − 1` lies in a
  prescribed set `S ⊆ ℤ` (so `VHat.deg W d = degSpan W {d}`, `degSpan_singleton`);
* `VHat.degSpan_lie_mem` — **the graded bracket**: if `d + e ∈ R` for all `d ∈ S`, `e ∈ T`, then
  `⁅degSpan S, degSpan T⁆ ⊆ degSpan R`.  It specializes to `VHat.deg_bracket_deg`
  (`⁅V̂(d), V̂(e)⁆ ⊆ V̂(d+e)`, DLM3 (3.2));
* `VHat.deepPart W n = ⨁_{p>n} V̂(−p)` and `VHat.parabolic W n = P_n`, together with the bundled
  Lie subalgebra `VHat.Pn W n` (DLM3 §4, the `P_n` of equation (4.1));
* `VHat.gen_eventually_deep` — for **every** `c : 𝒱` (not just homogeneous ones) the loop modes
  `c(m)` lie in the deep part for `m` large.  This is the lower-truncation engine of the induced
  module;
* the vacuum package `VHat.gen_vacuum_eq_zero` (`𝟙(m) = 0` for `m ≠ −1`, from `L₋₁𝟙 = 0`),
  `VHat.vacuumGen_mem_parabolic` (`𝟙(−1) ∈ P_n`) and `VHat.gen_vacuum_central`
  (`𝟙(−1)` is central in `V̂`) — the three facts behind DLM3's vacuum normalization on `M_n(U)`.

Everything is `sorry`-free, `pbw`-free and `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`).

## References
DLM3 (`q-alg/9612010v2`) §3 (3.1)–(3.3), §4 (4.1); H. Li `hep-th/9406211` §2;
`ZhuVermaAnArchVhat` (`VLoop`, `gen`, `deg`, `vhatBracket_gen`), `ZhuVermaAnArchVhatJac3`
(`lieRing`, `lieAlgebra`), `ZhuVermaAnArchMUVhat` (the scoped Lie instances, `uι`).
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## A `finsum` lands in a submodule as soon as every term does -/

/-- If every term of a family lies in a submodule, so does its `finsum` (the infinite-support
case being `0`).  Generic companion of `finsum_mem_submodule_dj`. -/
theorem finsum_mem_submodule {ι : Type*} {N : Type u} [AddCommGroup N] [Module ℂ N]
    {p : Submodule ℂ N} (f : ι → N) (h : ∀ i, f i ∈ p) : (∑ᶠ i, f i) ∈ p := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact Submodule.sum_mem _ fun i _ => h i
  · rw [finsum_of_infinite_support hs]
    exact p.zero_mem

/-! ## `degSpan` — the span of the generators with degrees in a prescribed set -/

/-- The span of the loop generators `a(m)` whose `V̂`-degree `wt a − m − 1` lies in `S ⊆ ℤ`.
`degSpan W {d}` is `VHat.deg W d`; `degSpan` over a downward set is DLM3's deep part, and over
`{0} ∪ (−∞, −n−1]` it is the parabolic `P_n` of DLM3 (4.1). -/
noncomputable def degSpan (W : VertexOperatorAlgebra 𝒱) (S : Set ℤ) :
    Submodule ℂ (VHatCarrier W) :=
  Submodule.span ℂ {x | ∃ (w m : ℤ) (a : 𝒱), a ∈ W.grading w ∧ w - m - 1 ∈ S ∧ x = gen W a m}

/-- A homogeneous generator lands in `degSpan S` as soon as its degree lies in `S`. -/
theorem gen_mem_degSpan (W : VertexOperatorAlgebra 𝒱) {S : Set ℤ} {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hS : w - m - 1 ∈ S) : gen W a m ∈ degSpan W S :=
  Submodule.subset_span ⟨w, m, a, ha, hS, rfl⟩

/-- `degSpan` is monotone in the degree set. -/
theorem degSpan_mono (W : VertexOperatorAlgebra 𝒱) {S T : Set ℤ} (h : S ⊆ T) :
    degSpan W S ≤ degSpan W T := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, m, a, ha, hS, rfl⟩
  exact gen_mem_degSpan W ha (h hS)

/-- `VHat.deg W d` is `degSpan` over the singleton `{d}`. -/
theorem degSpan_singleton (W : VertexOperatorAlgebra 𝒱) (d : ℤ) :
    degSpan W {d} = deg W d := rfl

/-! ## The graded bracket `⁅V̂(d), V̂(e)⁆ ⊆ V̂(d+e)` (DLM3 (3.2)) -/

/-- The OPE family occurring in `vhatBracket_gen` has finite support (VOA regularity). -/
theorem genOPE_support_finite (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (m k : ℤ) :
    (Function.support fun i : ℕ =>
      (gBinom m i) • gen W (W.smul a i b) (m + k - i)).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  exact hi (by
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), gen_zero_left, smul_zero])

/-- **The graded bracket of `V̂`.**  If `d + e ∈ R` whenever `d ∈ S` and `e ∈ T`, then the bracket
maps `degSpan S × degSpan T` into `degSpan R`.  This is DLM3 (3.2): `wt (a₍ᵢ₎b) = wt a + wt b −
i − 1` combined with the mode shift `m + k − i` makes every OPE term homogeneous of the *sum* of the
two degrees. -/
theorem degSpan_lie_mem (W : VertexOperatorAlgebra 𝒱) {S T R : Set ℤ}
    (hSTR : ∀ d ∈ S, ∀ e ∈ T, d + e ∈ R) {x y : VHatCarrier W}
    (hx : x ∈ degSpan W S) (hy : y ∈ degSpan W T) : ⁅x, y⁆ ∈ degSpan W R := by
  rw [bracket_eq]
  have hgen : ∀ (w m : ℤ) (a : 𝒱), a ∈ W.grading w → w - m - 1 ∈ S →
      ∀ z ∈ degSpan W T,
        vhatBracket W (bracketDescends W) (gen W a m) z ∈ degSpan W R := by
    intro w m a ha hdS z hz
    refine Submodule.span_induction
      (p := fun z _ => vhatBracket W (bracketDescends W) (gen W a m) z ∈ degSpan W R)
      ?_ ?_ ?_ ?_ hz
    · rintro z ⟨w', k, b, hb, heT, rfl⟩
      change vhatBracket W (bracketDescends W) (gen W a m) (gen W b k) ∈ degSpan W R
      rw [vhatBracket_gen W (bracketDescends W) a b m k]
      refine finsum_mem_submodule _ fun i => Submodule.smul_mem _ _ ?_
      refine gen_mem_degSpan W (w := w + w' - (i : ℤ) - 1)
        (W.toPreVertexAlgebra.smul_mem_grading ha hb (i : ℤ)) ?_
      rw [show w + w' - (i : ℤ) - 1 - (m + k - (i : ℤ)) - 1 = (w - m - 1) + (w' - k - 1) from by
        ring]
      exact hSTR _ hdS _ heT
    · change vhatBracket W (bracketDescends W) (gen W a m) (0 : VHatCarrier W) ∈ degSpan W R
      rw [map_zero]; exact Submodule.zero_mem _
    · intro y₁ y₂ _ _ h₁ h₂
      change vhatBracket W (bracketDescends W) (gen W a m) (y₁ + y₂) ∈ degSpan W R
      rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    · intro c y₁ _ h₁
      change vhatBracket W (bracketDescends W) (gen W a m) (c • y₁) ∈ degSpan W R
      rw [map_smul]; exact Submodule.smul_mem _ _ h₁
  refine Submodule.span_induction
    (p := fun x _ => vhatBracket W (bracketDescends W) x y ∈ degSpan W R) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨w, m, a, ha, hdS, rfl⟩; exact hgen w m a ha hdS y hy
  · change vhatBracket W (bracketDescends W) (0 : VHatCarrier W) y ∈ degSpan W R
    rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  · intro x₁ x₂ _ _ h₁ h₂
    change vhatBracket W (bracketDescends W) (x₁ + x₂) y ∈ degSpan W R
    rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ h₁ h₂
  · intro c x₁ _ h₁
    change vhatBracket W (bracketDescends W) (c • x₁) y ∈ degSpan W R
    rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ h₁

/-- **DLM3 (3.2), graded form**: `⁅V̂(d), V̂(e)⁆ ⊆ V̂(d+e)`. -/
theorem deg_bracket_deg (W : VertexOperatorAlgebra 𝒱) {d e : ℤ} {x y : VHatCarrier W}
    (hx : x ∈ deg W d) (hy : y ∈ deg W e) : ⁅x, y⁆ ∈ deg W (d + e) := by
  rw [← degSpan_singleton] at hx hy ⊢
  refine degSpan_lie_mem W ?_ hx hy
  intro d' hd' e' he'
  simp only [Set.mem_singleton_iff] at hd' he' ⊢
  omega

/-! ## The deep part and the parabolic `P_n` (DLM3 §4, equation (4.1)) -/

/-- The degree set of the **deep part** `⨁_{p > n} V̂(−p)`: degrees `≤ −n−1`. -/
def deepSet (n : ℕ) : Set ℤ := {d : ℤ | d ≤ -(n : ℤ) - 1}

/-- The degree set of the **parabolic** `P_n = V̂(0) ⊕ ⨁_{p > n} V̂(−p)`. -/
def parabolicSet (n : ℕ) : Set ℤ := {d : ℤ | d = 0 ∨ d ≤ -(n : ℤ) - 1}

theorem deepSet_subset_parabolicSet (n : ℕ) : deepSet n ⊆ parabolicSet n :=
  fun _ hd => Or.inr hd

/-- The parabolic degree set is closed under addition (`0 + 0 = 0`, `0 + e = e`, and
`d + e ≤ −2n−2 ≤ −n−1`). -/
theorem parabolicSet_add (n : ℕ) : ∀ d ∈ parabolicSet n, ∀ e ∈ parabolicSet n,
    d + e ∈ parabolicSet n := by
  have hn : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  rintro d (rfl | hd) e (rfl | he)
  · exact Or.inl (by ring)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)
  · exact Or.inr (by omega)

/-- **The deep part** `⨁_{p > n} V̂(−p)` of DLM3 §4: the span of the loop generators of degree
`≤ −n−1`.  It acts trivially on an `A_n(𝒱)`-module in DLM3's induced construction. -/
noncomputable def deepPart (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Submodule ℂ (VHatCarrier W) :=
  degSpan W (deepSet n)

/-- **The parabolic** `P_n = V̂(0) ⊕ ⨁_{p > n} V̂(−p)` of DLM3 (4.1), as a submodule. -/
noncomputable def parabolic (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : Submodule ℂ (VHatCarrier W) :=
  degSpan W (parabolicSet n)

theorem deepPart_le_parabolic (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    deepPart W n ≤ parabolic W n :=
  degSpan_mono W (deepSet_subset_parabolicSet n)

/-- **`P_n` as a Lie subalgebra of `V̂`** (DLM3 (4.1)): closure under the bracket is
`degSpan_lie_mem` applied to `parabolicSet_add`. -/
noncomputable def Pn (W : VertexOperatorAlgebra 𝒱) (n : ℕ) : LieSubalgebra ℂ (VHatCarrier W) :=
  { parabolic W n with
    lie_mem' := fun hx hy => degSpan_lie_mem W (parabolicSet_add n) hx hy }

@[simp] theorem mem_Pn (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (x : VHatCarrier W) :
    x ∈ Pn W n ↔ x ∈ parabolic W n := Iff.rfl

/-- A homogeneous generator of degree `0` lies in `P_n`. -/
theorem gen_mem_parabolic_of_deg_zero (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hd : w - m - 1 = 0) : gen W a m ∈ parabolic W n :=
  gen_mem_degSpan W ha (Or.inl hd)

/-- A homogeneous generator of degree `≤ −n−1` lies in the deep part. -/
theorem gen_mem_deepPart (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {w m : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading w) (hd : w - m - 1 ≤ -(n : ℤ) - 1) : gen W a m ∈ deepPart W n :=
  gen_mem_degSpan W ha hd

/-! ## Lower truncation: every loop mode is eventually deep -/

/-- **The truncation engine of DLM3's induced module.**  For *every* vector `c : 𝒱` — homogeneous
or not — the loop modes `c(m)` lie in the deep part `⨁_{p>n} V̂(−p)` once `m` is large.  (For a
homogeneous `c ∈ 𝒱_w` this is `m ≥ w + n`; the general case follows by internality of the grading.)
Since the deep part annihilates `U` in DLM3 (4.1), this is what makes `M_n(U)` a *lower truncated*
(i.e. field-theoretic) module. -/
theorem gen_eventually_deep (W : VertexOperatorAlgebra 𝒱) (n : ℕ) (c : 𝒱) :
    ∃ N : ℤ, ∀ m : ℤ, N ≤ m → gen W c m ∈ deepPart W n := by
  have hc : c ∈ ⨆ w : ℤ, W.grading w := by
    rw [W.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction W.grading
    (motive := fun c => ∃ N : ℤ, ∀ m : ℤ, N ≤ m → gen W c m ∈ deepPart W n) hc ?_ ?_ ?_
  · intro w a ha
    exact ⟨w + (n : ℤ), fun m hm => gen_mem_deepPart W n ha (by omega)⟩
  · exact ⟨0, fun m _ => by rw [gen_zero_left]; exact Submodule.zero_mem _⟩
  · rintro c₁ c₂ ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    refine ⟨max N₁ N₂, fun m hm => ?_⟩
    rw [gen_add_left]
    exact Submodule.add_mem _ (h₁ m (le_trans (le_max_left _ _) hm))
      (h₂ m (le_trans (le_max_right _ _) hm))

/-! ## The vacuum loop mode `𝟙(−1)` -/

/-- **`𝟙(m) = 0` for `m ≠ −1`.**  Immediate from the defining relation of `V̂`
(`gen_Lneg1`: `(L₋₁a)(m) = −m·a(m−1)`) applied to `L₋₁𝟙 = 0`. -/
theorem gen_vacuum_eq_zero (W : VertexOperatorAlgebra 𝒱) {m : ℤ} (hm : m ≠ -1) :
    gen W W.vacuum m = 0 := by
  have h := gen_Lneg1 W W.vacuum (m + 1)
  rw [L_neg_one_vacuum, gen_zero_left, show m + 1 - 1 = m from by ring] at h
  have hne : ((m + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : (m + 1 : ℤ) ≠ 0)
  have hc : (-((m + 1 : ℤ) : ℂ)) ≠ 0 := neg_ne_zero.mpr hne
  have h' : (-((m + 1 : ℤ) : ℂ)) • gen W W.vacuum m = 0 := h.symm
  calc gen W W.vacuum m
      = (-((m + 1 : ℤ) : ℂ))⁻¹ • ((-((m + 1 : ℤ) : ℂ)) • gen W W.vacuum m) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = (-((m + 1 : ℤ) : ℂ))⁻¹ • (0 : VHatCarrier W) := by rw [h']
    _ = 0 := smul_zero _

/-- `𝟙(−1)` lies in the parabolic `P_n` (it has degree `0 − (−1) − 1 = 0`). -/
theorem vacuumGen_mem_parabolic (W : VertexOperatorAlgebra 𝒱) (n : ℕ) :
    gen W W.vacuum (-1) ∈ parabolic W n :=
  gen_mem_parabolic_of_deg_zero W n W.vacuum_mem (by ring)

/-- **`𝟙(−1)` is central in `V̂`.**  Every OPE coefficient `𝟙₍ᵢ₎b` with `i ≥ 0` vanishes (VA2), so
the Borcherds bracket `⁅𝟙(−1), b(k)⁆` is the empty sum. -/
theorem gen_vacuum_central (W : VertexOperatorAlgebra 𝒱) (y : VHatCarrier W) :
    ⁅gen W W.vacuum (-1), y⁆ = 0 := by
  rw [bracket_eq]
  have hy : y ∈ Submodule.span ℂ (Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)) := by
    rw [gen_span_top]; exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun y _ =>
      vhatBracket W (bracketDescends W) (gen W W.vacuum (-1)) y = 0) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨⟨b, k⟩, rfl⟩
    change vhatBracket W (bracketDescends W) (gen W W.vacuum (-1)) (gen W b k) = 0
    rw [vhatBracket_gen W (bracketDescends W) W.vacuum b (-1) k]
    have hz : ∀ i : ℕ, W.smul W.vacuum (i : ℤ) b = 0 := by
      intro i
      rw [W.toPreVertexAlgebra.smul_vacuum_left (i : ℤ) b, if_neg (by omega : ((i : ℤ)) ≠ -1)]
    simp only [hz, gen_zero_left, smul_zero, finsum_zero]
  · change vhatBracket W (bracketDescends W) (gen W W.vacuum (-1)) (0 : VHatCarrier W) = 0
    rw [map_zero]
  · intro y₁ y₂ _ _ h₁ h₂
    change vhatBracket W (bracketDescends W) (gen W W.vacuum (-1)) (y₁ + y₂) = 0
    rw [map_add, h₁, h₂, add_zero]
  · intro c y₁ _ h₁
    change vhatBracket W (bracketDescends W) (gen W W.vacuum (-1)) (c • y₁) = 0
    rw [map_smul, h₁, smul_zero]

end VHat

end VOA

-- Axiom check (axiom-clean: [propext, Classical.choice, Quot.sound]).
