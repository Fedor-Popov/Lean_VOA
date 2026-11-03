/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.LatticeV1Simple
import VOA.AffineGeneral.Simple
import VOA.Foundations.CartanLattices
import VOA.Examples.DeligneLatticeLie

/-!
# Simple Lie algebras of types A₂, D₄, E₆, E₇, E₈ and their universal affine VOAs

For a symmetric Cartan matrix `G` (diagonal `2`, connected Dynkin diagram) the weight-one Lie algebra
`(V_L)₁` of the root lattice `L = ofCartan G` is simple (`cartan_isSimple`): the simple roots are the
standard basis vectors, which are roots, generate `ℤⁿ`, and are connected.  Connectivity is certified
by a distance function to a base node, checked by `decide`.

Instantiated for `a2`, `d4`, `e6`, `e7`, `e8` (`CartanLattices`); each gets `IsSimple`,
`FiniteDimensional`, and hence `standardAffineVOA` (`e8AffineVOA` etc.), the universal affine VOA
`V^k(𝔤)` in the normalization `Killing / (2 h∨)` for every `k ≠ -h∨`.
-/

namespace VOA.AffineGeneral.CartanSimple

open VOA VOA.LatGen VOA.CartanLattices VOA.AffineGeneral.LatticeLie

noncomputable section

variable {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hG : G.IsSymm)

theorem form_single (i j : Fin n) :
    (ofCartan G hG).form (Pi.single i 1) (Pi.single j 1) = G i j := by
  rw [ofCartan_form, Matrix.toBilin'_apply']
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem closure_single :
    AddSubgroup.closure (Set.range fun i : Fin n => (Pi.single i 1 : Fin n → ℤ)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [← Finset.univ_sum_single v]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  have : (Pi.single i (v i) : Fin n → ℤ) = v i • (Pi.single i 1 : Fin n → ℤ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this]
  exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _

/-- Reachability from a base node `i0`, certified by a distance function. -/
theorem reach_of_dist {r : Fin n → Fin n → Prop} (i0 : Fin n) (d : Fin n → ℕ)
    (hd : ∀ i, i = i0 ∨ ∃ j, d j < d i ∧ r j i) (i : Fin n) : Relation.ReflTransGen r i0 i := by
  induction h : d i using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    rcases hd i with rfl | ⟨j, hj, hr⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (ih (d j) (h ▸ hj) j rfl) hr

variable (hEven : (ofCartan G hG).Even) (hPos : (ofCartan G hG).PosDef)

/-- The simple roots `Pi.single i 1` of `ofCartan G`. -/
def simpleRoot (hdiag : ∀ i, G i i = 2) (i : Fin n) : Root (ofCartan G hG) hPos :=
  ⟨Pi.single i 1, (mem_normEq _ hPos).mpr (by rw [form_single, hdiag])⟩

/-- **The weight-one Lie algebra of a simply-laced root lattice with connected Dynkin diagram is
simple.** -/
theorem cartan_isSimple (hdiag : ∀ i, G i i = 2) (i0 : Fin n) (d : Fin n → ℕ)
    (hd : ∀ i, i = i0 ∨ ∃ j, d j < d i ∧ G j i ≠ 0) :
    LieAlgebra.IsSimple ℂ (V1 (ofCartan G hG) hEven hPos) := by
  haveI : Nonempty (Fin n) := ⟨i0⟩
  refine isSimple_of_simpleRoots hEven (simpleRoot G hG hPos hdiag)
    (closure_single (n := n)) ?_
  intro i j
  simp only [simpleRoot, form_single]
  have hsymm : ∀ a b, G a b ≠ 0 → G b a ≠ 0 := fun a b h => by
    rwa [← hG.apply b a]
  have hi : Relation.ReflTransGen (fun a b => G a b ≠ 0) i i0 :=
    Relation.ReflTransGen.symmetric hsymm (reach_of_dist i0 d hd i)
  exact hi.trans (reach_of_dist i0 d hd j)

theorem cartan_finiteDimensional (hdiag : ∀ i, G i i = 2) :
    FiniteDimensional ℂ (V1 (ofCartan G hG) hEven hPos) :=
  finiteDimensional_V1 hEven (rootsGenerate_of_simple (simpleRoot G hG hPos hdiag)
    (closure_single (n := n)))

/-! ## The five Deligne lattices -/

/-- `𝔰𝔩₃` as `(V_{A₂})₁`. -/
abbrev a2Lie : Type := V1 a2 a2_even a2_posDef
/-- `𝔰𝔬₈` as `(V_{D₄})₁`. -/
abbrev d4Lie : Type := V1 d4 d4_even d4_posDef
/-- `𝔢₆` as `(V_{E₆})₁`. -/
abbrev e6Lie : Type := V1 e6 e6_even e6_posDef
/-- `𝔢₇` as `(V_{E₇})₁`. -/
abbrev e7Lie : Type := V1 e7 e7_even e7_posDef
/-- `𝔢₈` as `(V_{E₈})₁`. -/
abbrev e8Lie : Type := V1 e8 e8_even e8_posDef

instance a2Lie_isSimple : LieAlgebra.IsSimple ℂ a2Lie :=
  cartan_isSimple _ _ _ _ (by decide) 0 ![0, 1] (by decide)

instance d4Lie_isSimple : LieAlgebra.IsSimple ℂ d4Lie :=
  cartan_isSimple _ _ _ _ (by decide) 1 ![1, 0, 1, 1] (by decide)

instance e6Lie_isSimple : LieAlgebra.IsSimple ℂ e6Lie :=
  cartan_isSimple _ _ _ _ (by decide) 3 ![2, 1, 1, 0, 1, 2] (by decide)

instance e7Lie_isSimple : LieAlgebra.IsSimple ℂ e7Lie :=
  cartan_isSimple _ _ _ _ (by decide) 3 ![2, 1, 1, 0, 1, 2, 3] (by decide)

instance e8Lie_isSimple : LieAlgebra.IsSimple ℂ e8Lie :=
  cartan_isSimple _ _ _ _ (by decide) 3 ![2, 1, 1, 0, 1, 2, 3, 4] (by decide)

instance a2Lie_finiteDimensional : FiniteDimensional ℂ a2Lie :=
  cartan_finiteDimensional _ _ _ _ (by decide)

instance d4Lie_finiteDimensional : FiniteDimensional ℂ d4Lie :=
  cartan_finiteDimensional _ _ _ _ (by decide)

instance e6Lie_finiteDimensional : FiniteDimensional ℂ e6Lie :=
  cartan_finiteDimensional _ _ _ _ (by decide)

instance e7Lie_finiteDimensional : FiniteDimensional ℂ e7Lie :=
  cartan_finiteDimensional _ _ _ _ (by decide)

instance e8Lie_finiteDimensional : FiniteDimensional ℂ e8Lie :=
  cartan_finiteDimensional _ _ _ _ (by decide)

/-! The same types as `DeligneLatticeLie.*Lie`: the instances apply there verbatim. -/

instance : LieAlgebra.IsSimple ℂ DeligneLatticeLie.a2Lie := a2Lie_isSimple
instance : LieAlgebra.IsSimple ℂ DeligneLatticeLie.d4Lie := d4Lie_isSimple
instance : LieAlgebra.IsSimple ℂ DeligneLatticeLie.e6Lie := e6Lie_isSimple
instance : LieAlgebra.IsSimple ℂ DeligneLatticeLie.e7Lie := e7Lie_isSimple
instance : LieAlgebra.IsSimple ℂ DeligneLatticeLie.e8Lie := e8Lie_isSimple

/-! ## Universal affine VOAs -/

/-- **`V^k(𝔢₈)`**, normalization `Killing/60` (`h∨ = 30`), for `k ≠ -30`. -/
def e8AffineVOA (k : ℂ) (hk : k + 30 ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData e8Lie 30 (by norm_num)) k) :=
  standardAffineVOA e8Lie 30 (by norm_num) k hk

/-- **`V^k(𝔢₇)`**, normalization `Killing/36` (`h∨ = 18`), for `k ≠ -18`. -/
def e7AffineVOA (k : ℂ) (hk : k + 18 ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData e7Lie 18 (by norm_num)) k) :=
  standardAffineVOA e7Lie 18 (by norm_num) k hk

/-- **`V^k(𝔢₆)`**, normalization `Killing/24` (`h∨ = 12`), for `k ≠ -12`. -/
def e6AffineVOA (k : ℂ) (hk : k + 12 ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData e6Lie 12 (by norm_num)) k) :=
  standardAffineVOA e6Lie 12 (by norm_num) k hk

/-- **`V^k(𝔰𝔬₈)`**, normalization `Killing/12` (`h∨ = 6`), for `k ≠ -6`. -/
def d4AffineVOA (k : ℂ) (hk : k + 6 ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData d4Lie 6 (by norm_num)) k) :=
  standardAffineVOA d4Lie 6 (by norm_num) k hk

/-- **`V^k(𝔰𝔩₃)`** via the `A₂` lattice, normalization `Killing/6` (`h∨ = 3`), for `k ≠ -3`. -/
def a2AffineVOA (k : ℂ) (hk : k + 3 ≠ 0) :
    VertexOperatorAlgebra (Vacuum (standardData a2Lie 3 (by norm_num)) k) :=
  standardAffineVOA a2Lie 3 (by norm_num) k hk

end

end VOA.AffineGeneral.CartanSimple
