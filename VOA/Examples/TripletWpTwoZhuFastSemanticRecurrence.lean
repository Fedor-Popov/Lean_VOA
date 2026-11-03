/- Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved. -/
import VOA.Examples.TripletWpTwoZhuFastSemanticMode

/-!
# Fast Zhu-omega semantics: recurrence transport

This layer contains no sparse coordinate expansion.  It propagates the one-step semantic
relation through the finite homogeneous recurrence and identifies its flattening with iterated
left Zhu multiplication by the conformal vector.
-/

namespace VOA.LatGen.WpTwoZhuFastSemantic

open scoped BigOperators
open VOA VOA.LatGen VOA.LatGen.Triplet
open VOA.IntegralLattice
open VOA.LatGen.Wp
open VOA.LatGen.WpC2
open VOA.SparseRational HeisenbergN
open VOA.LatGen.WpTwoAMSparseCompute
open VOA.LatGen.WpTwoZhuSparseCompute
open VOA.LatGen.WpTwoZhuSparseSemantics

private noncomputable abbrev Ltwo : IntegralLattice := latP 2

private theorem cbz_two_one : cbz (2 : ℤ) 1 = 2 := by
  rw [cbz_apply_nonneg (2 : ℤ) (by norm_num),
    show ((1 : ℤ)).toNat = 1 from rfl, gBinom]
  norm_num [Finset.prod_range_one]

private theorem cbz_two_two : cbz (2 : ℤ) 2 = 1 := by
  rw [cbz_apply_nonneg (2 : ℤ) (by norm_num),
    show ((2 : ℤ)).toNat = 2 from rfl, gBinom]
  norm_num [Finset.prod_range_succ, Finset.prod_range_one]

private theorem sum_range_three {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ Finset.range 3, f m = f 0 + f 1 + f 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]

private theorem zhuMul_conformal_three_modes {V : Type*} [AddCommGroup V]
    [Module ℂ V] (W : VertexOperatorAlgebra V) (v : V) :
    zhuMul W W.conformalVector v =
      W.smul W.conformalVector (-1) v +
        (2 : ℂ) • W.smul W.conformalVector 0 v +
          W.smul W.conformalVector 1 v := by
  rw [zhuMul_homogeneous' W W.conformal_mem]
  rw [show ((2 : ℤ).toNat + 1) = 3 from rfl, sum_range_three]
  have e0 : ((0 : ℕ) : ℤ) - 1 = -1 := by norm_num
  have e1 : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
  have e2 : ((2 : ℕ) : ℤ) - 1 = 1 := by norm_num
  have b0 : cbz (2 : ℤ) ((0 : ℕ) : ℤ) = 1 := by
    rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) by norm_num]
    exact cbz_zero 2
  have b1 : cbz (2 : ℤ) ((1 : ℕ) : ℤ) = 2 := by
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) by norm_num]
    exact cbz_two_one
  have b2 : cbz (2 : ℤ) ((2 : ℕ) : ℤ) = 1 := by
    rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
    exact cbz_two_two
  rw [e0, e1, e2, b0, b1, b2, one_smul, one_smul]

noncomputable def omegaPartsIntrinsic (hp : 1 ≤ 2) :
    ℕ → List (ℕ × (tripletW 2 hp).carrier)
  | 0 => [(0, (tripletWVOA 2 hp).vacuum)]
  | n + 1 => (omegaPartsIntrinsic hp n).flatMap (omegaPartIntrinsic hp)

noncomputable def flattenIntrinsic (hp : 1 ≤ 2)
    (xs : List (ℕ × (tripletW 2 hp).carrier)) : (tripletW 2 hp).carrier :=
  (xs.map Prod.snd).sum

private theorem flatten_omegaPartIntrinsic (hp : 1 ≤ 2)
    (x : ℕ × (tripletW 2 hp).carrier) :
    flattenIntrinsic hp (omegaPartIntrinsic hp x) =
      zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector x.2 := by
  rw [zhuMul_conformal_three_modes]
  simp [flattenIntrinsic, omegaPartIntrinsic]
  module

private theorem flatten_flatMap_omegaPartIntrinsic (hp : 1 ≤ 2) :
    ∀ xs : List (ℕ × (tripletW 2 hp).carrier),
      flattenIntrinsic hp (xs.flatMap (omegaPartIntrinsic hp)) =
        zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector
          (flattenIntrinsic hp xs)
  | [] => by simp [flattenIntrinsic]
  | x :: xs => by
      rw [List.flatMap_cons]
      change flattenIntrinsic hp
          (omegaPartIntrinsic hp x ++ xs.flatMap (omegaPartIntrinsic hp)) =
        zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector
          (x.2 + flattenIntrinsic hp xs)
      rw [zhuMul_add_right]
      rw [show flattenIntrinsic hp
          (omegaPartIntrinsic hp x ++ xs.flatMap (omegaPartIntrinsic hp)) =
            flattenIntrinsic hp (omegaPartIntrinsic hp x) +
              flattenIntrinsic hp (xs.flatMap (omegaPartIntrinsic hp)) by
        simp [flattenIntrinsic]]
      change flattenIntrinsic hp (omegaPartIntrinsic hp x) +
          flattenIntrinsic hp (xs.flatMap (omegaPartIntrinsic hp)) =
        zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector x.2 +
          zhuMul (tripletWVOA 2 hp) (tripletWVOA 2 hp).conformalVector
            (flattenIntrinsic hp xs)
      rw [flatten_omegaPartIntrinsic, flatten_flatMap_omegaPartIntrinsic]

private theorem flatten_omegaPartsIntrinsic_eq (hp : 1 ≤ 2) : ∀ n : ℕ,
    flattenIntrinsic hp (omegaPartsIntrinsic hp n) =
      zhuOmegaPow (tripletWVOA 2 hp) n
  | 0 => by simp [flattenIntrinsic, omegaPartsIntrinsic, zhuOmegaPow]
  | n + 1 => by
      rw [omegaPartsIntrinsic, flatten_flatMap_omegaPartIntrinsic,
        flatten_omegaPartsIntrinsic_eq, zhuOmegaPow]

theorem omegaPartsFast_rel (hp : 1 ≤ 2) : ∀ n : ℕ,
    List.Forall₂ (OmegaFastRel hp) (omegaPartsIntrinsic hp n)
      (WpTwoZhuSparseLhs.zhuOmegaPartsFastSparseQ n)
  | 0 => by
      simp only [omegaPartsIntrinsic,
        WpTwoZhuSparseLhs.zhuOmegaPartsFastSparseQ]
      constructor
      · refine ⟨rfl, (tripletWVOA 2 hp).vacuum_mem, ?_, ?_⟩
        · rw [tripletWVOA_vacuum_coe, evalZhuSparseQ_vacuumSparseQ]
          rfl
        · rw [evalZhuSparseQ_vacuumSparseQ]
          exact vacuumN_mem_gradingWN (rank Ltwo)
      exact List.Forall₂.nil
  | n + 1 => by
      rw [omegaPartsIntrinsic, WpTwoZhuSparseLhs.zhuOmegaPartsFastSparseQ]
      exact List.rel_flatMap (omegaPartsFast_rel hp n)
        (fun _ _ h => omegaPartFast_rel hp h)

private theorem flatten_rel_coe (hp : 1 ≤ 2)
    {xs : List (ℕ × (tripletW 2 hp).carrier)}
    {Ps : List (ℕ × SparseRational.Poly ℕ)}
    (h : List.Forall₂ (OmegaFastRel hp) xs Ps) :
    ((flattenIntrinsic hp xs : (tripletW 2 hp).carrier) : LatModuleGen Ltwo) =
      latStateGen Ltwo (evalZhuSparseQ (flattenGradedSparseQ Ps)) 0 := by
  induction h with
  | nil =>
      change (0 : LatModuleGen Ltwo) =
        latStateGen Ltwo (evalZhuSparseQ (sumQ [])) 0
      rw [evalZhuSparseQ_sumQ]
      simp [latStateGen]
  | @cons x P xs Ps hrel hrest ih =>
      rcases hrel with ⟨_, _, hx, _⟩
      change (x.2 : LatModuleGen Ltwo) +
          (flattenIntrinsic hp xs : LatModuleGen Ltwo) =
        latStateGen Ltwo
          (evalZhuSparseQ (sumQ (P.2 :: Ps.map Prod.snd))) 0
      rw [evalZhuSparseQ_sumQ]
      simp only [List.map_cons, List.sum_cons, List.map_map]
      rw [← List.map_map]
      rw [← evalZhuSparseQ_sumQ (Ps.map Prod.snd)]
      rw [hx, ih, latStateGen_add_boson]
      simp [flattenGradedSparseQ]

theorem zhuOmegaPow_coe_eq_eval_fast (hp : 1 ≤ 2) (n : ℕ) :
    ((zhuOmegaPow (tripletWVOA 2 hp) n : (tripletW 2 hp).carrier) :
        LatModuleGen Ltwo) =
      latStateGen Ltwo
        (evalZhuSparseQ (WpTwoZhuSparseLhs.omegaPowerFastSparseQ n)) 0 := by
  rw [← flatten_omegaPartsIntrinsic_eq hp n]
  simpa only [WpTwoZhuSparseLhs.omegaPowerFastSparseQ] using
    (flatten_rel_coe hp (omegaPartsFast_rel hp n))

end VOA.LatGen.WpTwoZhuFastSemantic

section AxiomAudit
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.omegaPartsFast_rel
#print axioms VOA.LatGen.WpTwoZhuFastSemantic.zhuOmegaPow_coe_eq_eval_fast
end AxiomAudit
