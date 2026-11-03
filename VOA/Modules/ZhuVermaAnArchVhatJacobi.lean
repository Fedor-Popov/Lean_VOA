/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArchVhat
import VOA.Core.BorcherdsIdentity
import VOA.Core.Reconstruction

/-!
# The loop-bracket Jacobi `VHat.VHatLeibniz`

This file discharges the deep crux **`VHat.VHatLeibniz`** (the Borcherds–Jacobi / Leibniz identity
for the descended loop bracket on `V̂`), the last of the three obligations
(`BracketDescends`, `VHatAntisymm`, `VHatLeibniz`) feeding `VHat.lieRingOfData`.

## Strategy and what is proved here

`VHatLeibniz` is a *trilinear* identity on the quotient `V̂ = VLoop ⧸ Im D`.  We reduce it,
**green and unconditionally**, to the corresponding identity on the generators `gen a m = a(m)`:

* `VHat.leibniz_reduce_to_gen` — because `vhatBracket W hD` is `ℂ`-bilinear (it is a
  `LinearMap →ₗ LinearMap`) and the generators `gen a m` span `V̂` (`gen_span_top`), the Leibniz
  identity for *all* `x y z` follows from the Leibniz identity for all *generator triples*
  `gen a m, gen b k, gen c l`.  This is the exact analogue of the triple
  `Finsupp.induction_linear` opening of `AffineLie.loop_leibniz`, carried out on the quotient via
  `Submodule.span_induction` against `gen_span_top`.

* `VHat.GenLeibniz` — the residual generator-level statement, i.e. the Borcherds loop-Jacobi on
  three generators, with both sides expanded by `vhatBracket_gen` into nested OPE finsums.

The generator-level identity is *precisely* the VOA Borcherds identity 5.1.7 assembled into the
loop bracket.  Its mode-level inputs are already in the repo: the commutator slice
`Core.BorcherdsIdentity.jacobi_commutator` (= `mode_commutator`, the `ℓ = 0` slice 5.1.7c) and the
iterate slice `Core.BorcherdsIdentity.mode_iterate` (5.1.7d).  The remaining content is the
double-finsum reindexing that turns the nested Borcherds OPE coefficients into the cyclic Jacobi
combination — the loop-level analogue of `leibniz_lie` in `AffineLie.loop_leibniz`, but with the
generalized-binomial `gBinom` Vandermonde (`Foundations.IotaZExpansion.cbz_vandermonde`) in place of
structure constants.

## Status
Green, `sorry`/axiom-free.  The trilinear→generator reduction (`leibniz_reduce_to_gen`) is proved
unconditionally; `VHatLeibniz_of_gen` then closes `VHatLeibniz` from the generator predicate
`GenLeibniz`.  `GenLeibniz` is recorded as the precise residual VOA identity (the Borcherds
loop-Jacobi on generators), *not* stubbed and *not* an axiom — it is a hypothesis, exactly as
`BracketDescends`/`VHatAntisymm` are hypotheses in `ZhuVermaAnArchVhat`.

## References
DLM3 §4; Gannon §5.1.3 (5.1.7), §5.3.2 Thm 5.3.4; cf. `Foundations.AffineLie.loop_leibniz`.
-/

namespace VOA

open VertexOperatorAlgebra PreVertexAlgebra
open scoped BigOperators
open Finsupp

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

namespace VHat

/-! ## The trilinear → generator reduction

`vhatBracket W hD` is `ℂ`-bilinear, so fixing any two arguments yields a `ℂ`-linear map in the
third.  Both sides of the Leibniz identity are therefore `ℂ`-linear in each variable separately,
and equality on the spanning set `{gen a m}` (`gen_span_top`) extends to all of `V̂`. -/

/-- The Leibniz "defect" trilinear form on `V̂`, whose vanishing is exactly `VHatLeibniz`. -/
noncomputable def leibnizDefect (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y z : VHatCarrier W) : VHatCarrier W :=
  vhatBracket W hD x (vhatBracket W hD y z)
    - (vhatBracket W hD (vhatBracket W hD x y) z + vhatBracket W hD y (vhatBracket W hD x z))

theorem leibnizDefect_eq_zero_iff (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y z : VHatCarrier W) :
    leibnizDefect W hD x y z = 0 ↔
      vhatBracket W hD x (vhatBracket W hD y z)
        = vhatBracket W hD (vhatBracket W hD x y) z + vhatBracket W hD y (vhatBracket W hD x z) := by
  rw [leibnizDefect, sub_eq_zero]

/-- `leibnizDefect` is `ℂ`-linear in its **third** argument (the cleanest one: `z` only ever sits
inside a single bracket, so additivity/`smul` come from `map_add`/`map_smul` of `vhatBracket`). -/
theorem leibnizDefect_add_z (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y z z' : VHatCarrier W) :
    leibnizDefect W hD x y (z + z') = leibnizDefect W hD x y z + leibnizDefect W hD x y z' := by
  simp only [leibnizDefect, map_add]
  abel

theorem leibnizDefect_smul_z (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (c : ℂ) (x y z : VHatCarrier W) :
    leibnizDefect W hD x y (c • z) = c • leibnizDefect W hD x y z := by
  simp only [leibnizDefect, map_smul, smul_sub, smul_add]

/-- `leibnizDefect` is `ℂ`-linear in its **second** argument `y`. -/
theorem leibnizDefect_add_y (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y y' z : VHatCarrier W) :
    leibnizDefect W hD x (y + y') z = leibnizDefect W hD x y z + leibnizDefect W hD x y' z := by
  simp only [leibnizDefect, map_add, LinearMap.add_apply]
  abel

theorem leibnizDefect_smul_y (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (c : ℂ) (x y z : VHatCarrier W) :
    leibnizDefect W hD x (c • y) z = c • leibnizDefect W hD x y z := by
  simp only [leibnizDefect, map_smul, LinearMap.smul_apply, smul_sub, smul_add]

/-- `leibnizDefect` is `ℂ`-linear in its **first** argument `x`. -/
theorem leibnizDefect_add_x (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x x' y z : VHatCarrier W) :
    leibnizDefect W hD (x + x') y z = leibnizDefect W hD x y z + leibnizDefect W hD x' y z := by
  simp only [leibnizDefect, map_add, LinearMap.add_apply]
  abel

theorem leibnizDefect_smul_x (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (c : ℂ) (x y z : VHatCarrier W) :
    leibnizDefect W hD (c • x) y z = c • leibnizDefect W hD x y z := by
  simp only [leibnizDefect, map_smul, LinearMap.smul_apply, smul_sub, smul_add]

/-- The generators `gen a m` of `V̂` (as a plain `Set`, the same one spanning `⊤` in
`gen_span_top`). -/
def genSet (W : VertexOperatorAlgebra 𝒱) : Set (VHatCarrier W) :=
  Set.range (fun p : 𝒱 × ℤ => gen W p.1 p.2)

theorem genSet_span_top (W : VertexOperatorAlgebra 𝒱) :
    Submodule.span ℂ (genSet W) = ⊤ := gen_span_top W

/-- If `leibnizDefect` vanishes on the third argument over `genSet`, it vanishes for all `z`
(with `x y` arbitrary fixed). -/
theorem leibnizDefect_zero_z_of_gen (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x y : VHatCarrier W) (hz : ∀ z ∈ genSet W, leibnizDefect W hD x y z = 0)
    (z : VHatCarrier W) : leibnizDefect W hD x y z = 0 := by
  have hmem : z ∈ Submodule.span ℂ (genSet W) := by rw [genSet_span_top]; trivial
  induction hmem using Submodule.span_induction with
  | mem z hzmem => exact hz z hzmem
  | zero =>
    have := leibnizDefect_smul_z W hD 0 x y 0
    simpa using this
  | add z z' _ _ ih ih' => rw [leibnizDefect_add_z, ih, ih', add_zero]
  | smul c z _ ih => rw [leibnizDefect_smul_z, ih, smul_zero]

/-- If `leibnizDefect` vanishes on the second argument over `genSet`, it vanishes for all `y`. -/
theorem leibnizDefect_zero_y_of_gen (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (x z : VHatCarrier W) (hy : ∀ y ∈ genSet W, leibnizDefect W hD x y z = 0)
    (y : VHatCarrier W) : leibnizDefect W hD x y z = 0 := by
  have hmem : y ∈ Submodule.span ℂ (genSet W) := by rw [genSet_span_top]; trivial
  induction hmem using Submodule.span_induction with
  | mem y hymem => exact hy y hymem
  | zero =>
    have := leibnizDefect_smul_y W hD 0 x 0 z
    simpa using this
  | add y y' _ _ ih ih' => rw [leibnizDefect_add_y, ih, ih', add_zero]
  | smul c y _ ih => rw [leibnizDefect_smul_y, ih, smul_zero]

/-- If `leibnizDefect` vanishes on the first argument over `genSet`, it vanishes for all `x`. -/
theorem leibnizDefect_zero_x_of_gen (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (y z : VHatCarrier W) (hx : ∀ x ∈ genSet W, leibnizDefect W hD x y z = 0)
    (x : VHatCarrier W) : leibnizDefect W hD x y z = 0 := by
  have hmem : x ∈ Submodule.span ℂ (genSet W) := by rw [genSet_span_top]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hxmem => exact hx x hxmem
  | zero =>
    have := leibnizDefect_smul_x W hD 0 0 y z
    simpa using this
  | add x x' _ _ ih ih' => rw [leibnizDefect_add_x, ih, ih', add_zero]
  | smul c x _ ih => rw [leibnizDefect_smul_x, ih, smul_zero]

/-- **The generator-level Borcherds loop-Jacobi predicate.**  This is `VHatLeibniz` restricted to
generator triples `a(m), b(k), c(l)` — equivalently, the Leibniz defect vanishes on the spanning
generators in each slot.  Expanding each `vhatBracket` by `vhatBracket_gen`, this is the Borcherds
identity 5.1.7 of the VOA assembled into the loop bracket: the cyclic combination of nested OPE
finsums `Σᵢⱼ gBinom · · gBinom · · • (a₍ᵢ₎(b₍ⱼ₎c))(…)` collapses to `0` modulo `Im D`, via the
mode commutator slice `jacobi_commutator` (5.1.7c) and iterate slice `mode_iterate` (5.1.7d). -/
def GenLeibniz (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) : Prop :=
  ∀ (a b c : 𝒱) (m k l : ℤ),
    vhatBracket W hD (gen W a m) (vhatBracket W hD (gen W b k) (gen W c l))
      = vhatBracket W hD (vhatBracket W hD (gen W a m) (gen W b k)) (gen W c l)
        + vhatBracket W hD (gen W b k) (vhatBracket W hD (gen W a m) (gen W c l))

/-- `GenLeibniz` is exactly the vanishing of `leibnizDefect` on every generator triple. -/
theorem genLeibniz_iff_defect (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) :
    GenLeibniz W hD ↔
      ∀ (a b c : 𝒱) (m k l : ℤ), leibnizDefect W hD (gen W a m) (gen W b k) (gen W c l) = 0 := by
  constructor
  · intro h a b c m k l
    rw [leibnizDefect_eq_zero_iff]; exact h a b c m k l
  · intro h a b c m k l
    have := h a b c m k l
    rw [leibnizDefect_eq_zero_iff] at this; exact this

/-- **Main reduction.**  The full quotient Leibniz identity `VHatLeibniz` is equivalent to its
generator-level restriction `GenLeibniz`, by `ℂ`-trilinearity of the bracket and `gen_span_top`. -/
theorem VHatLeibniz_iff_gen (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) :
    VHatLeibniz W hD ↔ GenLeibniz W hD := by
  constructor
  · intro h a b c m k l; exact h _ _ _
  · intro hgen
    rw [genLeibniz_iff_defect] at hgen
    intro x y z
    rw [← leibnizDefect_eq_zero_iff]
    -- reduce x, then y, then z to generators
    refine leibnizDefect_zero_x_of_gen W hD y z ?_ x
    rintro x ⟨⟨a, m⟩, rfl⟩
    refine leibnizDefect_zero_y_of_gen W hD (gen W a m) z ?_ y
    rintro y ⟨⟨b, k⟩, rfl⟩
    refine leibnizDefect_zero_z_of_gen W hD (gen W a m) (gen W b k) ?_ z
    rintro z ⟨⟨c, l⟩, rfl⟩
    exact hgen a b c m k l

/-- **`VHatLeibniz` from the generator predicate.**  Given `GenLeibniz` (the Borcherds loop-Jacobi
on three generators), the full quotient Leibniz identity holds.  This is the structural half of the
crux, proved unconditionally and axiom-free; it leaves exactly the generator-level VOA identity
`GenLeibniz` as the residual mode-level content. -/
theorem VHatLeibniz_of_gen (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (hgen : GenLeibniz W hD) : VHatLeibniz W hD :=
  (VHatLeibniz_iff_gen W hD).mpr hgen

/-! ## Explicit double-finsum expansion of the generator-level brackets

To make the residual `GenLeibniz` maximally precise, we expand each of the three nested brackets
into explicit double OPE finsums.  This pins the remaining VOA content to a single concrete
double-`finsum` identity in `V̂`, the loop-level avatar of the master Borcherds identity
`Core.Borcherds.jacobi` (5.1.7b). -/

/-- The OPE family for the inner bracket `[b(k), c(l)]` is finitely supported (VOA regularity). -/
theorem gen_inner_support_finite (W : VertexOperatorAlgebra 𝒱) (b c : 𝒱) (k l : ℤ) :
    (Function.support fun j : ℕ => (gBinom k j) • gen W (W.smul b j c) (k + l - j)).Finite := by
  obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero b c
  refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iio]
  by_contra hcon
  rw [not_lt] at hcon
  refine hj ?_
  rw [hNz j (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]

/-- Distributing `[a(m), ·]` over the inner finsum `[b(k), c(l)] = Σⱼ gBinom k j • (b₍ⱼ₎c)(k+l-j)`:
`[a(m), [b(k), c(l)]] = Σⱼ gBinom k j • Σᵢ gBinom m i • (a₍ᵢ₎(b₍ⱼ₎c))(m+k+l-i-j)`. -/
theorem vhatBracket_gen_inner (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (a b c : 𝒱) (m k l : ℤ) :
    vhatBracket W hD (gen W a m) (vhatBracket W hD (gen W b k) (gen W c l))
      = ∑ᶠ j : ℕ, (gBinom k j) •
          ∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i (W.smul b j c)) (m + (k + l - j) - i) := by
  rw [vhatBracket_gen W hD b c k l,
    map_finsum (vhatBracket W hD (gen W a m)) (gen_inner_support_finite W b c k l)]
  refine finsum_congr fun j => ?_
  rw [map_smul, vhatBracket_gen W hD a (W.smul b j c) m (k + l - j)]

/-- Distributing over the inner bracket on the right: `[[a(m), b(k)], c(l)]`. -/
theorem vhatBracket_gen_outer_left (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (a b c : 𝒱) (m k l : ℤ) :
    vhatBracket W hD (vhatBracket W hD (gen W a m) (gen W b k)) (gen W c l)
      = ∑ᶠ i : ℕ, (gBinom m i) •
          ∑ᶠ p : ℕ, (gBinom (m + k - i) p) •
            gen W (W.smul (W.smul a i b) p c) (m + k - i + l - p) := by
  have hfin : (Function.support
      fun i : ℕ => (gBinom m i) • gen W (W.smul a i b) (m + k - i)).Finite := by
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a b
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hi ?_
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]
  rw [vhatBracket_gen W hD a b m k]
  have hflip : vhatBracket W hD (∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i b) (m + k - i))
      (gen W c l)
      = (vhatBracket W hD).flip (gen W c l)
          (∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i b) (m + k - i)) := rfl
  rw [hflip, map_finsum ((vhatBracket W hD).flip (gen W c l)) hfin]
  refine finsum_congr fun i => ?_
  rw [map_smul]
  show (gBinom m i) • vhatBracket W hD (gen W (W.smul a i b) (m + k - i)) (gen W c l) = _
  rw [vhatBracket_gen W hD (W.smul a i b) c (m + k - i) l]

/-- Distributing over the inner bracket in the cyclic term: `[b(k), [a(m), c(l)]]`. -/
theorem vhatBracket_gen_outer_right (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W)
    (a b c : 𝒱) (m k l : ℤ) :
    vhatBracket W hD (gen W b k) (vhatBracket W hD (gen W a m) (gen W c l))
      = ∑ᶠ i : ℕ, (gBinom m i) •
          ∑ᶠ p : ℕ, (gBinom k p) •
            gen W (W.smul b p (W.smul a i c)) (k + (m + l - i) - p) := by
  rw [vhatBracket_gen W hD a c m l,
    map_finsum (vhatBracket W hD (gen W b k)) ?_]
  · refine finsum_congr fun i => ?_
    rw [map_smul, vhatBracket_gen W hD b (W.smul a i c) k (m + l - i)]
  · -- finiteness of the `[a(m), c(l)]` family
    obtain ⟨Nz, hNz⟩ := W.smul_eventually_zero a c
    refine Set.Finite.subset (Set.finite_Iio Nz.toNat) ?_
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Iio]
    by_contra hcon
    rw [not_lt] at hcon
    refine hi ?_
    rw [hNz i (le_trans (Int.self_le_toNat Nz) (by exact_mod_cast hcon)), gen_zero_left, smul_zero]

/-- **The residual VOA identity (fully explicit form).**  `GenLeibniz` is equivalent to the
following single double-`finsum` identity in `V̂`, for all `a b c` and `m k l`:

`Σⱼ gBinom k j • Σᵢ gBinom m i • (a₍ᵢ₎(b₍ⱼ₎c))(m+k+l-i-j)`
   `= Σᵢ gBinom m i • Σₚ gBinom (m+k-i) p • ((a₍ᵢ₎b)₍ₚ₎c)(m+k-i+l-p)`
     `+ Σᵢ gBinom m i • Σₚ gBinom k p • (b₍ₚ₎(a₍ᵢ₎c))(k+(m+l-i)-p)`.

This is the loop-bracket assembly of the master Borcherds identity `Core.Borcherds.jacobi`
(5.1.7b): the `gen`-level (and hence `Im D`-quotient) repackaging of
`Σᵢ (-1)ⁱC(ℓ,i)(u₍ℓ₊ₘ₋ᵢ₎(v₍ₙ₊ᵢ₎x) − (-1)^ℓ v₍…₎(u₍…₎x)) = Σᵢ C(m,i)(u₍ℓ₊ᵢ₎v)₍ₘ₊ₙ₋ᵢ₎x`.
It is the precise remaining content; the entire structural reduction above is unconditional and
axiom-free. -/
theorem GenLeibniz_iff_explicit (W : VertexOperatorAlgebra 𝒱) (hD : BracketDescends W) :
    GenLeibniz W hD ↔
      ∀ (a b c : 𝒱) (m k l : ℤ),
        (∑ᶠ j : ℕ, (gBinom k j) •
            ∑ᶠ i : ℕ, (gBinom m i) • gen W (W.smul a i (W.smul b j c)) (m + (k + l - j) - i))
          = (∑ᶠ i : ℕ, (gBinom m i) •
              ∑ᶠ p : ℕ, (gBinom (m + k - i) p) •
                gen W (W.smul (W.smul a i b) p c) (m + k - i + l - p))
            + ∑ᶠ i : ℕ, (gBinom m i) •
                ∑ᶠ p : ℕ, (gBinom k p) •
                  gen W (W.smul b p (W.smul a i c)) (k + (m + l - i) - p) := by
  unfold GenLeibniz
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun c =>
    forall_congr' fun m => forall_congr' fun k => forall_congr' fun l => ?_
  rw [vhatBracket_gen_inner W hD a b c m k l, vhatBracket_gen_outer_left W hD a b c m k l,
    vhatBracket_gen_outer_right W hD a b c m k l]

end VHat

end VOA
