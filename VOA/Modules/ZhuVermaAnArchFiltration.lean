/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modules.ZhuVermaAnArch
import VOA.Modules.ZhuVermaAnDescent15

/-!
# The surjection filtration `A_n(𝒱) ↠ A₀(𝒱)`.

The Dong–Li–Mason filtration of the level-`n` Frenkel–Zhu algebras (J. Algebra 206 (1998), Prop. 2.4):
the identity map `𝒱 → 𝒱` descends to an algebra surjection
`A_n(𝒱) = 𝒱 / OnFull 𝒱 n  ↠  A₀(𝒱) = 𝒱 / OnFull 𝒱 0`
precisely because `OnFull 𝒱 n ⊆ OnFull 𝒱 0`.

This file collects the parts of `OnFull W n ⊆ OnFull W 0` that follow from the existing library, and
isolates the single remaining genuine VOA computation.

## What is proved here (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `OnL_le_On_zero` : `OnL W ≤ On W 0`.  Every `(L₋₁a + L₀a)` is `zhuMul W (L₋₁a+L₀a) 𝟙` (vacuum right
  unit) which lies in `On W 0` by `gen_mem_On_zero`.
* `OnFull_zero_eq_On_zero` : `OnFull W 0 = On W 0` (`= O W` via `On_zero_eq_O`).  The `OnL`-generator
  family is redundant at level `0` (DLM eq. 2.1 remark).
* `OnFull_le_OnFull_zero_of_circ` : the `comap`/`span_le` reduction of `OnFull W n ⊆ OnFull W 0` to the
  single circle-generator membership `∀ c d, circ W n c d ∈ OnFull W 0`.  (The `OnL`-generator family
  of `OnFull W n` is the SAME family for every `n`, already `≤ On W 0 = OnFull W 0`.)
* `An_to_A0` / `An_to_A0_surjective` : GIVEN the circle membership, the descended algebra surjection
  `A_n(𝒱) ↠ A₀(𝒱)` and its surjectivity (`Submodule.factor`/`mapQ` of the inclusion).

## The single remaining target (the genuine DLM Prop. 2.4 pole-reduction, NOT faked, NOT axiomatized)

`circ_mem_OnFull_zero : ∀ c d, circ W n c d ∈ OnFull W 0` — equivalently `circ W n c d ∈ O W`.

For homogeneous `a ∈ 𝒱_M`, `circ W n a b = ∑_{i=0}^{M+n} C(M+n,i) · a₍ᵢ₋₂ₙ₋₂₎ b`
`= Res_z Y(a,z)b (1+z)^{M+n} / z^{2n+2}`.  This is the FZ residue with **numerator power `M+n`** and
**pole order `2n+2`**, i.e. an *excess* `e := (M+n) - (M) = n` over the diagonal pole `z^{2}` of the
defining `O(𝒱)`-generator `Res_z Y(a,z)b (1+z)^{M}/z^{2} = (L₋₁a+L₀a)*b`.

The library's higher-pole keystone `Pres_mem_O` (`ZhuModule`, FZ Lemma 2.1.2) only covers the
**excess-`0`** diagonal `Pres W M a b k = Res_z Y(a,z)b (1+z)^{M+k}/z^{2+k} ∈ O W` (numerator and pole
shift TOGETHER by `k`).  All integration-by-parts recursions available in the repo (`pres_coeff_identity`,
`presOn_coeff_identity`, `smul_L_neg_one`) are **excess-preserving**: they move `(M, k) ↦ (M+1, k)`
(`a ↦ L₋₁a`) or shift numerator and pole in lock-step, so they connect only members of the same excess.
`circ W n` has excess `n ≥ 1`, which is NOT reachable from the excess-`0` `Pres` family by these moves.

The genuine missing content is the DLM pole-reduction `circ W n a b ∈ O W` via the
`(L₋₁ + L₀ + (M+n)) `-generator step that lowers the *excess* by one (DLM Prop. 2.4 / FZ Lemma 2.1.2 in
its two-parameter `(top, pole)` form).  It requires either (i) a two-parameter residue family
`PG W M a b T m := ∑_i C(T,i) a₍ᵢ₋₂₋ₘ₎ b` together with the excess-lowering recursion
`(T + 1 - 2 - m) · PG(T, m) = PG_{L₋₁a}(T,m) + (T)·PG(T-1, m) + (boundary)` proven `∈ O W` for
`m ≥ T - M`, or (ii) the explicit `(L₋₁+L₀)`-modulo telescoping of DLM Prop. 2.4.  Neither is in the
repo; both are flagged here as the precise frontier (status: partial), not closed with a placeholder.
-/

namespace VOA

open VertexOperatorAlgebra
open scoped BigOperators

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## `OnL ≤ On 0`: the `(L₋₁+L₀)` family is in Zhu's `O(𝒱)`. -/

/-- **`OnL W ≤ On W 0`.**  Each generator `(L₋₁a + L₀a)` equals `zhuMul W (L₋₁a+L₀a) 𝟙` by the vacuum
right-unit (`zhuMul_vacuum_right`), and that lands in `On W 0` by `gen_mem_On_zero`.  (At level `0` the
DLM `(L₋₁+L₀)`-generator family is redundant — it is `u ∘₀ 𝟙 ∈ O(𝒱)`.) -/
theorem OnL_le_On_zero (W : VertexOperatorAlgebra 𝒱) : OnL W ≤ On W 0 := by
  rw [OnL, Submodule.span_le]
  rintro x ⟨a, rfl⟩
  have h := gen_mem_On_zero W a W.vacuum
  rwa [zhuMul_vacuum_right W (W.L (-1) a + W.L 0 a)] at h

/-- **`OnFull W 0 = On W 0`.**  The corrected `O₀` collapses to the circle-only span at level `0`
because the `(L₋₁+L₀)` family is already inside it (`OnL_le_On_zero`). -/
theorem OnFull_zero_eq_On_zero (W : VertexOperatorAlgebra 𝒱) : OnFull W 0 = On W 0 := by
  rw [OnFull, sup_eq_left]
  exact OnL_le_On_zero W

/-- `OnFull W 0 = O W` (the corrected `O₀` is Zhu's `O(𝒱)`). -/
theorem OnFull_zero_eq_O (W : VertexOperatorAlgebra 𝒱) : OnFull W 0 = O W := by
  rw [OnFull_zero_eq_On_zero, On_zero_eq_O]

/-! ## `OnL ≤ OnFull 0` and the reduction of the full inclusion to the circle generators. -/

/-- The level-independent `(L₋₁+L₀)` family of `OnFull W n` already lies in `OnFull W 0`. -/
theorem OnL_le_OnFull_zero (W : VertexOperatorAlgebra 𝒱) : OnL W ≤ OnFull W 0 :=
  le_trans (OnL_le_On_zero W) (On_le_OnFull W 0)

/-- **Reduction of the filtration inclusion to the circle generators.**  `OnFull W n ⊆ OnFull W 0`
follows from `∀ c d, circ W n c d ∈ OnFull W 0` (the only `n`-dependent generators): split
`OnFull W n = On W n ⊔ OnL W`; the `OnL` summand is `≤ OnFull W 0` unconditionally
(`OnL_le_OnFull_zero`), and `On W n = span{circ W n}` is `≤ OnFull W 0` by `span_le` once each circle
generator is. -/
theorem OnFull_le_OnFull_zero_of_circ (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hcirc : ∀ c d : 𝒱, circ W n c d ∈ OnFull W 0) :
    OnFull W n ≤ OnFull W 0 := by
  rw [OnFull, sup_le_iff]
  refine ⟨?_, OnL_le_OnFull_zero W⟩
  rw [On_eq_span, Submodule.span_le]
  rintro x ⟨c, d, rfl⟩
  exact hcirc c d

/-! ## The descended algebra surjection `A_n(𝒱) ↠ A₀(𝒱)` (given the circle membership). -/

/-- **`A_n(𝒱) ↠ A₀(𝒱)`**, GIVEN `OnFull W n ⊆ OnFull W 0`.  The identity `𝒱 → 𝒱` descends along the
two quotients because the level-`n` relations map to `0` in `A₀` (inclusion of submodules).  Realized
as `Submodule.mapQ id` of the inclusion `hle`. -/
noncomputable def AnFull_to_A0 (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hle : OnFull W n ≤ OnFull W 0) :
    (𝒱 ⧸ OnFull W n) →ₗ[ℂ] (𝒱 ⧸ OnFull W 0) :=
  Submodule.mapQ (OnFull W n) (OnFull W 0) LinearMap.id hle

/-- The filtration surjection is surjective (it is `mkQ` precomposed with the identity, up to the
quotient map): every class in `A₀` lifts to `𝒱`, hence to `A_n`, and maps back to itself. -/
theorem AnFull_to_A0_surjective (W : VertexOperatorAlgebra 𝒱) (n : ℕ)
    (hle : OnFull W n ≤ OnFull W 0) :
    Function.Surjective (AnFull_to_A0 W n hle) := by
  intro y
  obtain ⟨v, rfl⟩ := (OnFull W 0).mkQ_surjective y
  refine ⟨(OnFull W n).mkQ v, ?_⟩
  simp [AnFull_to_A0, Submodule.mapQ_apply]

/-! ## The two-parameter FZ residue family and its excess-lowering recursion (proved engine).

The DLM Prop. 2.4 pole-reduction is driven by the two-parameter residue
`Gres W a b T p := ∑_{i=0}^{T} C(T,i) · a₍ᵢ₋ₚ₎ b = Res_z Y(a,z)b (1+z)^T / z^p`
(numerator top `T`, pole `p`).  `circ W n a b = Gres W a b (M+n) (2n+2)` for `a ∈ 𝒱_M`
(`circ_eq_Gres`).  The engine is the **excess-lowering recursion** (`Gres_recursion`)
`(p-1) • Gres a T p = Gres_{L₋₁a} T (p-1) + T • Gres a (T-1) (p-1)`,
proved here from `smul_L_neg_one` (translation) and `cbz_upper_absorption` (the `i·C(T,i)=T·C(T-1,i-1)`
binomial identity) — NO abstract residue/integration lemma.  Both right-hand families have strictly
smaller *excess* `T - M` than the left (the first via `a ↦ L₋₁a`, `M ↦ M+1`; the second via
`T ↦ T-1`), so this is the recursion that an induction-on-excess closure of `circ W n ∈ O W` runs on.
-/

/-- **`Gres W a b T p`** — the FZ residue `∑_{i=0}^{T} C(T,i)·a₍ᵢ₋ₚ₎b = Res_z Y(a,z)b (1+z)^T/z^p`,
with numerator top `T : ℕ` and pole `p : ℕ` as free parameters. -/
noncomputable def Gres (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (T p : ℕ) : 𝒱 :=
  ∑ i ∈ Finset.range (T + 1), cbz (T : ℤ) (i : ℤ) • W.smul a ((i : ℤ) - p) b

/-- For homogeneous `a ∈ 𝒱_M`, `circ W n a b = Gres W a b (M+n) (2n+2)` (numerator `(1+z)^{M+n}`,
pole `z^{2n+2}`; mode `i - (2n+2) = i - 2n - 2`). -/
theorem circ_eq_Gres (W : VertexOperatorAlgebra 𝒱) (n : ℕ) {M : ℕ} {a : 𝒱}
    (ha : a ∈ W.grading (M : ℤ)) (b : 𝒱) :
    circ W n a b = Gres W a b (M + n) (2 * n + 2) := by
  rw [circ_homogeneous W n ha b, Gres,
    show ((M : ℤ) + (n : ℤ)).toNat + 1 = M + n + 1 from by
      rw [show ((M : ℤ) + (n : ℤ)) = ((M + n : ℕ) : ℤ) from by push_cast; ring, Int.toNat_natCast]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((M : ℤ) + (n : ℤ)) = ((M + n : ℕ) : ℤ) from by push_cast; ring,
    show ((i : ℤ) - 2 * (n : ℤ) - 2) = ((i : ℤ) - ((2 * n + 2 : ℕ) : ℤ)) from by push_cast; ring]

/-- **The excess-lowering recursion (★★).**  For `T ≥ 1` and `p ≥ 1`:
`(p-1) • Gres a T p = Gres_{L₋₁a} T (p-1) + T • Gres a (T-1) (p-1)`.
Proof: expand the `L₋₁a`-term via `smul_L_neg_one` ((L₋₁a)₍ₖ₎ = -k·a₍ₖ₋₁₎); reindex the `T•Gres(T-1)`
term onto `range(T+1)` (the new bottom `i=0` term vanishes, `C(T-1,-1)=0`); per mode `a₍ᵢ₋ₚ₎b` the
scalar identity is `(p-1)·C(T,i) = (p-1-i)·C(T,i) + T·C(T-1,i-1)`, i.e. the upper absorption
`i·C(T,i) = T·C(T-1,i-1)` (`cbz_upper_absorption`). -/
theorem Gres_recursion (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) (T p : ℕ) (hT : 1 ≤ T) (hp : 1 ≤ p) :
    ((p : ℂ) - 1) • Gres W a b T p
      = Gres W (W.L (-1) a) b T (p - 1) + (T : ℂ) • Gres W a b (T - 1) (p - 1) := by
  -- term1 expanded via smul_L_neg_one onto mode a₍ᵢ₋ₚ₎b over range(T+1)
  have hpsub : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by push_cast [Nat.cast_sub hp]; ring
  have hL : Gres W (W.L (-1) a) b T (p - 1)
      = ∑ i ∈ Finset.range (T + 1),
          (cbz (T : ℤ) (i : ℤ) * (-((i : ℂ) - p + 1))) • W.smul a ((i : ℤ) - p) b := by
    unfold Gres
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpsub, smul_L_neg_one W a b ((i : ℤ) - ((p : ℤ) - 1)),
      show ((i : ℤ) - ((p : ℤ) - 1) - 1) = (i : ℤ) - p from by ring,
      ← Int.cast_smul_eq_zsmul ℂ (-((i : ℤ) - ((p : ℤ) - 1))) (W.smul a ((i : ℤ) - p) b), smul_smul]
    congr 2; push_cast; ring
  -- term2 reindexed onto range(T+1)
  have hTsub : ((T - 1 : ℕ) : ℤ) = (T : ℤ) - 1 := by push_cast [Nat.cast_sub hT]; ring
  have hR : (T : ℂ) • Gres W a b (T - 1) (p - 1)
      = ∑ i ∈ Finset.range (T + 1),
          ((T : ℂ) * cbz ((T : ℤ) - 1) ((i : ℤ) - 1)) • W.smul a ((i : ℤ) - p) b := by
    unfold Gres
    rw [Finset.smul_sum, show T - 1 + 1 = T from by omega]
    rw [Finset.sum_range_succ' (fun i => ((T : ℂ) * cbz ((T : ℤ) - 1) ((i : ℤ) - 1))
          • W.smul a ((i : ℤ) - p) b) T]
    rw [show cbz ((T : ℤ) - 1) ((0 : ℕ) - 1 : ℤ) = 0 from cbz_apply_neg _ (by norm_num),
      mul_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, hTsub, hpsub]
    congr 2
    · push_cast; ring
    · push_cast; ring
  -- LHS expanded over range(T+1)
  have hLHS : ((p : ℂ) - 1) • Gres W a b T p
      = ∑ i ∈ Finset.range (T + 1),
          (((p : ℂ) - 1) * cbz (T : ℤ) (i : ℤ)) • W.smul a ((i : ℤ) - p) b := by
    unfold Gres; rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; rw [smul_smul]
  rw [hLHS, hL, hR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← add_smul]; congr 1
  have hua := cbz_upper_absorption T (i : ℤ)
  push_cast at hua ⊢
  linear_combination hua

/-! ## Status

`OnFull W n ⊆ OnFull W 0` is REDUCED (axiom-clean) to the single circle membership
`∀ c d, circ W n c d ∈ OnFull W 0` (`OnFull_le_OnFull_zero_of_circ`), and the descended surjection
`A_n ↠ A₀` is built from any proof of that inclusion (`AnFull_to_A0`, `AnFull_to_A0_surjective`).  The
`OnL`-generator side is fully closed (`OnL_le_On_zero`, `OnFull_zero_eq_On_zero`).

The remaining circle membership `circ W n c d ∈ O W` is the DLM Prop. 2.4 pole-reduction.  As proved in
the docstring above, the repo's higher-pole keystone `Pres_mem_O` covers only the *excess-0* diagonal;
`circ W n` has *excess `n`*, unreachable from `Pres` by the available excess-preserving
integration-by-parts recursions.  Closing it needs the two-parameter `(top, pole)` FZ residue family
with its excess-lowering recursion (a new development), or the explicit `(L₋₁+L₀)`-modulo telescoping of
DLM Prop. 2.4.  This is the precise frontier — flagged, not faked.
-/

end VOA
