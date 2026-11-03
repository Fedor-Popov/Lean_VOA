/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Foundations.LatticeCocycle
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Bounded vectors of an even positive-definite lattice are finite  (`BoundedFinite`)

The one analytic input for the general lattice-VOA `L₀`-grading (`Examples.LatticeGenGrading`):
for a positive-definite integral lattice `L`, `{α : L | ⟨α,α⟩ ≤ N}` is finite (`boundedFinite`).

Route (no `ZLattice` needed — a direct coordinate box-bound): fix the `ℤ`-basis `B = latticeBasis L`
with Gram matrix `G i j = ⟨Bᵢ,Bⱼ⟩`, so `⟨α,α⟩ = coord α ⬝ᵥ G *ᵥ coord α` with `coord α = B.repr α`.
`L.PosDef` ⟹ `G` positive on `ℤʳ\0`; the **`ℤ⇒ℝ` bridge** (density + `det`-kernel) gives `G`
positive on `ℝʳ\0`; then **coercivity** (min on the sphere) yields `m>0` with `m·‖c‖² ≤ Qℝ(c)`, so
`⟨α,α⟩ ≤ N` forces every coordinate into a fixed finite box.

## References
* FLM Ch. 8; Conway–Sloane; Gannon §1.2.1.
-/

set_option linter.style.longLine false

namespace VOA.IntegralLattice

open scoped BigOperators Matrix
open Module

variable (L : IntegralLattice)

/-- The rank (index cardinality of `latticeBasis L`). -/
noncomputable def latRank : ℕ := Fintype.card (Module.Free.ChooseBasisIndex ℤ L.carrier)

/-- The integer Gram matrix `G i j = ⟨Bᵢ,Bⱼ⟩` in the chosen basis. -/
noncomputable def gram : Matrix (Fin (latRank L)) (Fin (latRank L)) ℤ :=
  Matrix.of fun i j => L.form (latticeBasis L i) (latticeBasis L j)

/-- The coordinate vector `coord α = (B.repr α)ᵢ`. -/
noncomputable def coord (α : L.carrier) : Fin (latRank L) → ℤ := fun i => (latticeBasis L).repr α i

/-- `coord` is a `ℤ`-linear bijection onto `Fin r → ℤ` (basis coordinates). -/
theorem coord_injective : Function.Injective (coord L) := by
  intro α β h
  apply (latticeBasis L).repr.injective
  ext i
  exact congrFun h i

/-- The Gram identity `⟨α,α⟩ = coord α ⬝ᵥ G *ᵥ coord α`. -/
theorem form_eq_gram (α : L.carrier) :
    L.form α α = coord L α ⬝ᵥ (gram L *ᵥ coord L α) := by
  rw [form_eq_sum_repr L (latticeBasis L) α α]
  simp only [dotProduct, Matrix.mulVec, gram, coord, Matrix.of_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **`G` is positive on `ℤʳ \ 0`** (from `L.PosDef`): `0 < v ⬝ᵥ G *ᵥ v` for `v ≠ 0`. -/
theorem gram_pos_int (hPos : L.PosDef) (v : Fin (latRank L) → ℤ) (hv : v ≠ 0) :
    0 < v ⬝ᵥ (gram L *ᵥ v) := by
  -- v = coord α for α = ∑ vᵢ Bᵢ ≠ 0
  set α : L.carrier := (latticeBasis L).equivFun.symm v with hα
  have h1 : (latticeBasis L).equivFun α = v := by rw [hα]; exact LinearEquiv.apply_symm_apply _ _
  have hcoord : coord L α = v := by
    funext i
    have hi := congrFun h1 i
    simp only [Basis.equivFun_apply] at hi
    rw [coord]; exact hi
  have hαne : α ≠ 0 := by
    rw [hα, Ne, LinearEquiv.map_eq_zero_iff]; exact hv
  rw [← hcoord, ← form_eq_gram]
  exact hPos α hαne

/-! ## The real Gram form and the box finiteness from coercivity -/

/-- The real Gram matrix `Gℝ = G.map (Int.cast)`. -/
noncomputable def gramR : Matrix (Fin (latRank L)) (Fin (latRank L)) ℝ :=
  (gram L).map (Int.cast)

/-- The real quadratic form `Qℝ(c) = c ⬝ᵥ Gℝ *ᵥ c`. -/
noncomputable def Qr (c : Fin (latRank L) → ℝ) : ℝ := c ⬝ᵥ (gramR L *ᵥ c)

/-- On integer coordinates, `Qℝ` matches the integer form: `Qℝ(v) = (v ⬝ᵥ G *ᵥ v : ℤ)`. -/
theorem Qr_intCast (v : Fin (latRank L) → ℤ) :
    Qr L (fun i => (v i : ℝ)) = ((v ⬝ᵥ (gram L *ᵥ v) : ℤ) : ℝ) := by
  simp only [Qr, gramR, dotProduct, Matrix.mulVec, Matrix.map_apply, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum]

/-- **Coercivity of the real Gram form** (the analytic input): `∃ m > 0, m·‖c‖² ≤ Qℝ(c)`. -/
def Coercive : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ c : Fin (latRank L) → ℝ, m * (∑ i, (c i) ^ 2) ≤ Qr L c

/-- **`BoundedFinite` from coercivity** — the box bound.  If `m·‖v‖² ≤ Qℝ(v)` and `Qℝ(v) ≤ N`, every
coordinate satisfies `vⱼ² ≤ ⌊N/m⌋`, hence `|vⱼ| ≤ ⌊N/m⌋`, so `{α | ⟨α,α⟩ ≤ N}` sits in a finite box. -/
theorem boundedFinite_of_coercive (_hPos : L.PosDef) (hc : Coercive L) : BoundedFinite L := by
  obtain ⟨m, hm, hcoer⟩ := hc
  intro N
  -- reduce to the coordinate set via the injection `coord`
  have hpre : {α : L.carrier | L.form α α ≤ N}
      = coord L ⁻¹' {v : Fin (latRank L) → ℤ | v ⬝ᵥ (gram L *ᵥ v) ≤ N} := by
    ext α; simp only [Set.mem_setOf_eq, Set.mem_preimage, form_eq_gram]
  rw [hpre]
  apply Set.Finite.preimage (Function.Injective.injOn (coord_injective L))
  -- the coordinate set is finite: bound each coordinate by `M := ⌊N/m⌋`
  set M : ℤ := ⌊(N : ℝ) / m⌋ with hM
  apply Set.Finite.subset (s := Set.pi Set.univ (fun _ : Fin (latRank L) => Set.Icc (-M) M))
  · exact Set.Finite.pi (fun _ => Set.finite_Icc _ _)
  · intro v hv
    simp only [Set.mem_setOf_eq] at hv
    intro j _
    -- from coercivity: ∑ (vᵢ:ℝ)² ≤ N/m, so (vⱼ)² ≤ ⌊N/m⌋ =: M
    have hQ : Qr L (fun i => (v i : ℝ)) ≤ (N : ℝ) := by
      rw [Qr_intCast]; exact_mod_cast hv
    have hsum : m * (∑ i, ((v i : ℝ)) ^ 2) ≤ (N : ℝ) := le_trans (hcoer _) hQ
    have hsumle : (∑ i, ((v i : ℝ)) ^ 2) ≤ (N : ℝ) / m := by
      rw [le_div_iff₀ hm, mul_comm]; exact hsum
    have hj : ((v j : ℝ)) ^ 2 ≤ (N : ℝ) / m :=
      le_trans (Finset.single_le_sum (f := fun i => ((v i : ℝ)) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)) hsumle
    have hj2 : (v j) ^ 2 ≤ M := by
      rw [hM, Int.le_floor]; push_cast; exact hj
    -- |vⱼ| ≤ vⱼ² ≤ M, via the consecutive-integer products `vⱼ(vⱼ±1) ≥ 0`
    have hplus : 0 ≤ v j * (v j + 1) := by
      rcases lt_or_ge (v j) 0 with h | h
      · nlinarith [mul_nonneg (show (0:ℤ) ≤ -v j by omega) (show (0:ℤ) ≤ -(v j + 1) by omega)]
      · exact mul_nonneg (by omega) (by omega)
    have hminus : 0 ≤ v j * (v j - 1) := by
      rcases lt_or_ge (v j) 1 with h | h
      · nlinarith [mul_nonneg (show (0:ℤ) ≤ -v j by omega) (show (0:ℤ) ≤ -(v j - 1) by omega)]
      · exact mul_nonneg (by omega) (by omega)
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · nlinarith [hplus, hj2]
    · nlinarith [hminus, hj2]

/-! ## Discharging coercivity from `L.PosDef` -/

/-- `Qℝ` is continuous. -/
theorem Qr_continuous : Continuous (Qr L) :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- `Qℝ` is homogeneous of degree 2: `Qℝ(t·c) = t²·Qℝ(c)`. -/
theorem Qr_smul (t : ℝ) (c : Fin (latRank L) → ℝ) : Qr L (t • c) = t ^ 2 * Qr L c := by
  simp only [Qr, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- `G` is non-negative on all of `ℤʳ` (`= 0` at `0`, `> 0` elsewhere). -/
theorem gram_nonneg_int (hPos : L.PosDef) (v : Fin (latRank L) → ℤ) :
    0 ≤ v ⬝ᵥ (gram L *ᵥ v) := by
  rcases eq_or_ne v 0 with h | h
  · subst h; simp [dotProduct, Matrix.mulVec]
  · exact le_of_lt (gram_pos_int L hPos v h)

/-- Clearing denominators: every rational coordinate vector `q` has a common denominator `n > 0`
with `q i · n = vᵢ ∈ ℤ`. -/
theorem exists_common_den (q : Fin (latRank L) → ℚ) :
    ∃ (n : ℤ) (v : Fin (latRank L) → ℤ), 0 < n ∧ ∀ i, q i * (n : ℚ) = (v i : ℚ) := by
  refine ⟨∏ j, ((q j).den : ℤ), fun i => (q i).num * ((∏ j, ((q j).den : ℤ)) / ((q i).den : ℤ)),
    Finset.prod_pos (fun j _ => by exact_mod_cast (q j).den_pos), fun i => ?_⟩
  have hden : ((q i).den : ℤ) ≠ 0 := by exact_mod_cast (q i).den_pos.ne'
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun j => ((q j).den : ℤ)) (Finset.mem_univ i)
  have hnum : q i * ((q i).den : ℚ) = ((q i).num : ℚ) := by
    have hdenQ : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_pos.ne'
    have h := Rat.num_div_den (q i)
    rw [div_eq_iff hdenQ] at h
    exact h.symm
  have hvi : (q i).num * ((∏ j, ((q j).den : ℤ)) / ((q i).den : ℤ)) = (q i).num * m := by
    rw [hm, Int.mul_ediv_cancel_left _ hden]
  dsimp only
  rw [hvi, hm]
  push_cast
  rw [← mul_assoc, hnum]

/-- **`Qℝ ≥ 0`** (positive semidefiniteness), by density of `ℚʳ`: `Qℝ ≥ 0` on the rational points
(each is `(1/n)·(integer vector)`, so `Qℝ = (1/n²)·(integer form) ≥ 0`), and `{Qℝ ≥ 0}` is closed. -/
theorem Qr_nonneg (hPos : L.PosDef) (c : Fin (latRank L) → ℝ) : 0 ≤ Qr L c := by
  have hclosed : IsClosed {x : Fin (latRank L) → ℝ | 0 ≤ Qr L x} :=
    isClosed_le continuous_const (Qr_continuous L)
  have hrat : ∀ q : Fin (latRank L) → ℚ,
      0 ≤ Qr L (Pi.map (fun _ => (Rat.cast : ℚ → ℝ)) q) := by
    intro q
    obtain ⟨n, v, hn, hqv⟩ := exists_common_den L q
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have heq : Pi.map (fun _ => (Rat.cast : ℚ → ℝ)) q
        = (1 / (n : ℝ)) • (fun i => (v i : ℝ)) := by
      funext i
      simp only [Pi.map_apply, Pi.smul_apply, smul_eq_mul]
      have := hqv i
      field_simp
      exact_mod_cast this
    rw [heq, Qr_smul, Qr_intCast]
    have : 0 ≤ ((v ⬝ᵥ (gram L *ᵥ v) : ℤ) : ℝ) := by exact_mod_cast gram_nonneg_int L hPos v
    positivity
  have hsub : closure (Set.range (Pi.map (fun _ : Fin (latRank L) => (Rat.cast : ℚ → ℝ))))
      ⊆ {x | 0 ≤ Qr L x} := hclosed.closure_subset_iff.mpr (Set.range_subset_iff.mpr hrat)
  exact hsub ((DenseRange.piMap (fun _ => Rat.denseRange_cast)) c)

/-- `Gℝ` is symmetric. -/
theorem gramR_symm : (gramR L)ᵀ = gramR L := by
  ext i j
  simp only [Matrix.transpose_apply, gramR, Matrix.map_apply, gram, Matrix.of_apply]
  rw [form_symm L (latticeBasis L j) (latticeBasis L i)]

/-- The associated bilinear form is symmetric: `u ⬝ᵥ Gℝ *ᵥ w = w ⬝ᵥ Gℝ *ᵥ u`. -/
theorem Bform_symm (u w : Fin (latRank L) → ℝ) :
    u ⬝ᵥ (gramR L *ᵥ w) = w ⬝ᵥ (gramR L *ᵥ u) := by
  simp only [dotProduct, Matrix.mulVec, gramR, Matrix.map_apply, gram, Matrix.of_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
  rw [form_symm L (latticeBasis L i) (latticeBasis L j)]
  ring

/-- **`Qℝ` is positive-definite** (`0 < Qℝ c` for `c ≠ 0`).  From `Qℝ ≥ 0`: if `Qℝ c = 0` then the
quadratic `t ↦ Qℝ(c + t·y) ≥ 0` (min at `t=0`) forces `Gℝᵀ *ᵥ c = 0`, hence `det G = 0`, hence `G` is
singular over `ℚ` — clearing denominators gives a nonzero **integer** kernel vector `w`, whence
`w ⬝ᵥ G *ᵥ w = 0`, contradicting `gram_pos_int`. -/
theorem Qr_pos (hPos : L.PosDef) {c : Fin (latRank L) → ℝ} (hc : c ≠ 0) : 0 < Qr L c := by
  rcases (Qr_nonneg L hPos c).lt_or_eq with h | h
  · exact h
  exfalso
  have hsymm : ∀ u w, u ⬝ᵥ (gramR L *ᵥ w) = w ⬝ᵥ (gramR L *ᵥ u) := Bform_symm L
  have hcc : c ⬝ᵥ (gramR L *ᵥ c) = 0 := h.symm
  -- Step A: `Gℝ *ᵥ c = 0` via the quadratic minimum at `t = 0`.
  have hB : ∀ y, c ⬝ᵥ (gramR L *ᵥ y) = 0 := by
    intro y
    have hexp : ∀ t : ℝ, Qr L (c + t • y)
        = (c ⬝ᵥ (gramR L *ᵥ c))
          + (2 * t * (c ⬝ᵥ (gramR L *ᵥ y)) + t ^ 2 * (y ⬝ᵥ (gramR L *ᵥ y))) := by
      intro t
      simp only [Qr, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hsymm y c]; ring
    have hquad : ∀ t : ℝ, 0 ≤ 2 * t * (c ⬝ᵥ (gramR L *ᵥ y)) + t ^ 2 * (y ⬝ᵥ (gramR L *ᵥ y)) := by
      intro t
      have hnn := Qr_nonneg L hPos (c + t • y)
      rw [hexp, hcc] at hnn; linarith
    have hAnn : 0 ≤ y ⬝ᵥ (gramR L *ᵥ y) := Qr_nonneg L hPos y
    rcases eq_or_lt_of_le hAnn with hA0 | hA0
    · have h1 := hquad 1; have h2 := hquad (-1); rw [← hA0] at h1 h2
      refine le_antisymm ?_ ?_ <;> nlinarith [h1, h2]
    · set A := y ⬝ᵥ (gramR L *ᵥ y) with hA_def
      set B := c ⬝ᵥ (gramR L *ᵥ y) with hB_def
      have hk := hquad (-B / A)
      have hAne : A ≠ 0 := ne_of_gt hA0
      have hAB : A * (2 * (-B / A) * B + (-B / A) ^ 2 * A) = -B ^ 2 := by field_simp; ring
      have hnb : 0 ≤ -B ^ 2 := by rw [← hAB]; exact mul_nonneg (le_of_lt hA0) hk
      exact pow_eq_zero_iff (by norm_num) |>.mp (le_antisymm (by linarith) (sq_nonneg B))
  -- `Gℝ *ᵥ c = 0`
  have hGc : gramR L *ᵥ c = 0 := by
    have hself : (gramR L *ᵥ c) ⬝ᵥ (gramR L *ᵥ c) = 0 := by
      rw [hsymm (gramR L *ᵥ c) c]; exact hB (gramR L *ᵥ c)
    exact dotProduct_self_eq_zero.mp hself
  -- `det G = 0`
  have hdet : (gram L).det = 0 := by
    have hdetR : (gramR L).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨c, hc, hGc⟩
    have hcast : (gramR L).det = ((gram L).det : ℝ) :=
      (RingHom.map_det (Int.castRingHom ℝ) (gram L)).symm
    rw [hcast] at hdetR; exact_mod_cast hdetR
  -- a nonzero **rational** kernel vector of `G`
  have hdetQ : ((gram L).map (Int.castRingHom ℚ)).det = 0 := by
    have hc2 : ((gram L).det : ℚ) = ((gram L).map (Int.castRingHom ℚ)).det :=
      RingHom.map_det (Int.castRingHom ℚ) (gram L)
    rw [← hc2, hdet]; simp
  obtain ⟨q, hq0, hqk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetQ
  -- clear denominators to an integer kernel vector `w` (`(w i : ℚ) = q i · n`)
  obtain ⟨n, w, hn, hnw⟩ := exists_common_den L q
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hwk : gram L *ᵥ w = 0 := by
    funext i
    have key : ((gram L *ᵥ w) i : ℚ)
        = (n : ℚ) * (((gram L).map (Int.castRingHom ℚ)) *ᵥ q) i := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Int.coe_castRingHom, Int.cast_sum,
        Int.cast_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← hnw j]; ring
    rw [hqk] at key
    simp only [Pi.zero_apply, mul_zero] at key
    have : ((gram L *ᵥ w) i : ℚ) = ((0 : Fin (latRank L) → ℤ) i : ℚ) := by rw [key]; simp
    exact_mod_cast this
  have hw0 : w ≠ 0 := by
    intro hw
    apply hq0
    funext i
    have hi := hnw i
    rw [hw] at hi
    simp only [Pi.zero_apply, Int.cast_zero] at hi
    rcases mul_eq_zero.mp hi with h' | h'
    · simp only [Pi.zero_apply]; exact h'
    · exact absurd h' hnQ
  have hcontra := gram_pos_int L hPos w hw0
  rw [hwk, dotProduct_zero] at hcontra
  exact absurd hcontra (lt_irrefl 0)

/-- **Coercivity** `Coercive L` holds — from positive-definiteness `Qr_pos` via the minimum of `Qℝ`
on the compact unit sphere `{∑ cᵢ² = 1}` (positive by `Qr_pos`), scaled up by homogeneity. -/
theorem coercive (hPos : L.PosDef) : Coercive L := by
  rcases Nat.eq_zero_or_pos (latRank L) with hr | hr
  · -- rank 0: everything is the empty sum
    haveI : IsEmpty (Fin (latRank L)) := hr ▸ (inferInstance : IsEmpty (Fin 0))
    exact ⟨1, one_pos, fun c => by
      simp only [Qr, dotProduct, Matrix.mulVec, Finset.univ_eq_empty, Finset.sum_empty, mul_zero,
        le_refl]⟩
  -- rank ≥ 1: minimize on the unit sphere
  set S : Set (Fin (latRank L) → ℝ) := {c | ∑ i, (c i) ^ 2 = 1} with hS
  have hScont : Continuous (fun c : Fin (latRank L) → ℝ => ∑ i, (c i) ^ 2) :=
    continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)
  have hScl : IsClosed S := isClosed_eq hScont continuous_const
  have hSbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun c hc => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hci2 : (c i) ^ 2 ≤ 1 := by
      rw [← (hc : ∑ j, (c j) ^ 2 = 1)]
      exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hci2
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hScl hSbd
  have hSne : S.Nonempty := by
    refine ⟨fun i => if i = (⟨0, hr⟩ : Fin (latRank L)) then 1 else 0, ?_⟩
    simp only [hS, Set.mem_setOf_eq]
    rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin (latRank L))]
    · simp
    · intro j _ hj; rw [if_neg hj]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  obtain ⟨c₀, hc₀S, hc₀min⟩ := hScomp.exists_isMinOn hSne (Qr_continuous L).continuousOn
  have hc₀ne : c₀ ≠ 0 := by
    intro h0; rw [h0] at hc₀S
    simp only [hS, Set.mem_setOf_eq, Pi.zero_apply] at hc₀S
    norm_num at hc₀S
  refine ⟨Qr L c₀, Qr_pos L hPos hc₀ne, fun c => ?_⟩
  rcases eq_or_ne (∑ i, (c i) ^ 2) 0 with hs0 | hs0
  · rw [hs0, mul_zero]; exact Qr_nonneg L hPos c
  · have hsp : 0 < ∑ i, (c i) ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hs0)
    set s := ∑ i, (c i) ^ 2 with hs_def
    have hsqrt_ne : Real.sqrt s ≠ 0 := Real.sqrt_ne_zero'.mpr hsp
    set nc := (1 / Real.sqrt s) • c with hnc
    have hnc_S : nc ∈ S := by
      change ∑ i, (nc i) ^ 2 = 1
      simp only [hnc, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, ← hs_def]
      rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hsp), one_div, inv_mul_cancel₀ (ne_of_gt hsp)]
    have hc_eq : c = Real.sqrt s • nc := by
      rw [hnc, smul_smul, mul_one_div, div_self hsqrt_ne, one_smul]
    have hQ : Qr L c = s * Qr L nc := by
      rw [hc_eq, Qr_smul, Real.sq_sqrt (le_of_lt hsp)]
    rw [hQ]
    have hmin : Qr L c₀ ≤ Qr L nc := (isMinOn_iff.mp hc₀min) nc hnc_S
    nlinarith [hmin, hsp]

/-- **Bounded lattice vectors are finite** — `BoundedFinite L`, unconditionally from `L.PosDef`. -/
theorem boundedFinite (hPos : L.PosDef) : BoundedFinite L :=
  boundedFinite_of_coercive L hPos (coercive L hPos)

end VOA.IntegralLattice
