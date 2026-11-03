/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroFixedReconstruction
import VOA.Examples.VirasoroGram56

/-!
# Actual word pairings and ordinary Gram-kernel relations

An ordinary Gram-kernel relation gives a state killed by the simple quotient.
Its lifted word expression need not vanish, but has only a tangent coordinate.
Ordinary adjointness therefore kills its pairing with the lifted adjoint word.
-/
namespace VOA.VirDeformModes
open VertexOperatorAlgebra Deform Module VirModule VirSimple
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Compose a finite list of Virasoro modes, in their written order. -/
noncomputable def virWord (L : ℤ → End ℂ V) : List ℤ → End ℂ V
  | [] => 1
  | n::w => L n * virWord L w

/-- Appending a word composes the two word operators. -/
theorem virWord_append (L : ℤ → End ℂ V) (w t : List ℤ) :
    virWord L (w++t) = virWord L w * virWord L t := by
  induction w with
  | nil => simp [virWord]
  | cons n w ih => simp [virWord, ih, mul_assoc]

/-- Adjointness reverses a Virasoro word and negates each mode index.
Unlike weight-one current adjointness, it introduces no sign per factor. -/
theorem virWord_adjoint {W : VertexOperatorAlgebra V} (B : InvariantForm W)
    (w : List ℤ) (x y : V) :
    B.form (virWord W.L w x) y =
      B.form x (virWord W.L (w.reverse.map Neg.neg) y) := by
  induction w generalizing y with
  | nil => rfl
  | cons n w ih =>
      simp only [virWord, Module.End.mul_apply, B.virasoro_adj, ih,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        virWord_append, mul_one]

/-- Ordinary coordinates of actual normalized words are ordinary Virasoro words. -/
theorem virWord_fst {W : VertexOperatorAlgebra V}
    (D : FirstOrderDeformation W) (β : ℂ) (w : List ℤ) (x : V × V) :
    (virWord (normalizedL D β) w x).1 = virWord W.L w x.1 := by
  induction w with
  | nil => rfl
  | cons n w ih => simp only [virWord, Module.End.mul_apply, normalizedL_apply, ih]

/-- On pure tangent states a normalized word acts by the ordinary word. -/
theorem virWord_tangent {W : VertexOperatorAlgebra V}
    (D : FirstOrderDeformation W) (β : ℂ) (w : List ℤ) (x : V) :
    virWord (normalizedL D β) w (0,x) = (0,virWord W.L w x) := by
  induction w with
  | nil => rfl
  | cons n w ih => simp only [virWord, Module.End.mul_apply, ih, normalizedL_tangent]

/-- A row relation in an actual homogeneous Gram matrix belongs to the maximal
ideal. Testing against a basis suffices, since other weights are orthogonal. -/
theorem gram_row_relation_mem_maxIdeal {W : VertexOperatorAlgebra V}
    (B : InvariantForm W) (hB : B.IsFullyInvariant) (hn : B.Normalized)
    {ι : Type*} [Fintype ι] {n : ℤ} (e : Basis ι ℂ (W.grading n)) (r : ι → ℂ)
    (hr : ∀ j, ∑ i, r i * B.form (e i : V) (e j : V) = 0) :
    (∑ i, r i • (e i : V)) ∈ QuotVOA.maxGradedIdeal W := by
  have hs : (∑ i, r i • (e i : V)) ∈ W.grading n :=
    Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (e i).property)
  apply (LiRadical.mem_maxGradedIdeal_iff_grading hB hn hs).mpr
  have hf : (B.form (∑ i, r i • (e i : V))).comp (W.grading n).subtype = 0 := by
    apply e.ext
    intro j
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply] using hr j
  intro y hy
  exact LinearMap.congr_fun hf ⟨y,hy⟩

/-- The simple quotient intertwines every finite Virasoro word. -/
theorem virWord_mkQ (c : ℂ) (w : List ℤ) (v : VirUniv c) :
    (maxIdealVir c).mkQ (virWord (virasoroVOA c).L w v) =
      virWord (virasoroSimple c).L w ((maxIdealVir c).mkQ v) := by
  induction w with
  | nil => rfl
  | cons n w ih => simp only [virWord, Module.End.mul_apply, VirQuotForm.mkQ_L, ih]

/-- An ordinary finite word relation forces the actual lifted adjoint pairing
to vanish. The lifted relation is only pure tangent; no deformed invariant
form or vanishing of the lifted state itself is assumed. -/
theorem virWord_pairing_obstruction {W : VertexOperatorAlgebra V}
    (D : FirstOrderDeformation W) (β : ℂ) (B : InvariantForm W)
    {ι : Type*} [Fintype ι] (w : ι → List ℤ) (r : ι → ℂ)
    (hr : ∑ i, r i • virWord W.L (w i) W.vacuum = 0) :
    B.form W.vacuum
      ((∑ i, r i • virWord (normalizedL D β) ((w i).reverse.map Neg.neg))
        (∑ j, r j • virWord (normalizedL D β) (w j) (W.vacuum,0))).2 = 0 := by
  let x := ∑ j, r j • virWord (normalizedL D β) (w j) (W.vacuum,0)
  have hx : x = (0,x.2) := by
    apply Prod.ext
    · simpa only [x, Prod.fst_sum, Prod.smul_fst, virWord_fst] using hr
    · rfl
  change B.form W.vacuum ((∑ i, r i • virWord (normalizedL D β)
    ((w i).reverse.map Neg.neg)) x).2 = 0
  rw [hx]
  have hh := congrArg (fun z => B.form z x.2) hr
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, virWord_tangent,
    Prod.snd_sum, Prod.smul_snd, map_sum, map_smul, smul_eq_mul,
    virWord_adjoint, map_zero, LinearMap.zero_apply] using hh

end VOA.VirDeformModes
