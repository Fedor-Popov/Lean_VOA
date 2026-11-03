import VOA.Huang.LogAssocFivePointBlockFiber
import VOA.Huang.LogAssocFivePointTensorMap
import VOA.Huang.LogAssocFivePointChart
import VOA.Huang.LogAssocFivePointFirstEdge
import VOA.Huang.LogAssocFivePointLastEdge
import VOA.Huang.LogAssocFivePointPointFibers

/-! Actual fixed-weight sewing edges for the concrete logarithmic pentagon
chart. All terms are genuine canonical point blocks, with the true finite
logarithmic sums and actual tensor morphisms. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Huang.LogAssocFivePoint
open CategoryTheory VOA.LogTensor VOA.LogTensor.Pz VOA.LogTensor.Contra VOA.LogTensor.LogModuleCat
open VOA.C2Rigid.LocalInjective VOA.Huang.LogAssocExpansion
open VOA.Huang.LogAssocFivePointChart VOA.Huang.LogAssocFivePointFunctionals
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (hC2 : C2Cofinite W)

-- Actual fourfold categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The actual inner associator tensored with the fourth identity. -/
def fiveEdge01 (N P Q R : LogModuleCat W) :
    fivePointObject hC2 N P Q R .left ⟶ fivePointObject hC2 N P Q R .inner :=
  tensorMorphism hC2 (associatorIso hC2 N P Q).hom (𝟙 R)

-- Actual fourfold categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The actual reassociation after freezing the second-third tensor input. -/
def fiveEdge12 (N P Q R : LogModuleCat W) :
    fivePointObject hC2 N P Q R .inner ⟶ fivePointObject hC2 N P Q R .middle :=
  (associatorIso hC2 N (tensorObject hC2 P Q) R).hom

-- Actual fourfold categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The actual last-three associator tensored with the first identity. -/
def fiveEdge23 (N P Q R : LogModuleCat W) :
    fivePointObject hC2 N P Q R .middle ⟶ fivePointObject hC2 N P Q R .right :=
  tensorMorphism hC2 (𝟙 N) (associatorIso hC2 P Q R).hom

-- Actual fourfold categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The actual first-second tensor treated as the first reassociation input. -/
def fiveEdge04 (N P Q R : LogModuleCat W) :
    fivePointObject hC2 N P Q R .left ⟶ fivePointObject hC2 N P Q R .pair :=
  (associatorIso hC2 (tensorObject hC2 N P) Q R).hom

-- Actual fourfold categorical tensor types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The actual last-two tensor treated as the third reassociation input. -/
def fiveEdge43 (N P Q R : LogModuleCat W) :
    fivePointObject hC2 N P Q R .pair ⟶ fivePointObject hC2 N P Q R .right :=
  (associatorIso hC2 N P (tensorObject hC2 Q R)).hom

-- Actual fixed-weight fourfold block types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The true first pentagon fiber follows from completed logarithmic
associativity in the scaled real chart, for every scalar output test. -/
theorem fiberEdge01 (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .inner →ₗ[ℂ] ℂ) (δ : ℂ) :
    (∑' γ : ℂ,fivePointTerm hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (fiveEdge01 hC2 N P Q R).1) γ δ)=
    ∑' γ : ℂ,fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s f γ δ := by
  let T := tensorObject hC2 N P
  let L := tensorObject hC2 T Q
  let S := tensorObject hC2 P Q
  let H := tensorObject hC2 N S
  let α := (associatorIso hC2 N P Q).hom
  let J := tensorIntertwiner hC2 H.act R.act H.finiteGeneration R.finiteGeneration
  let φ := frozenPointFunctional H.act R.act (tensorObject hC2 H R).act J 0 δ d β f w
  have hs : 0<s := hD.1.trans hD.2.1
  let t : ℂ := (Real.log (r/s) : ℝ)
  have ht : t∈VOA.Huang.AssocExpansion.overlapDomain := positive_ratio_mem_overlap hD.1 hs hD.2.1
  have hchart := positive_ratio_chart hD.1 hs
  have he := tensorAssociatorHom_completed_shift (β := δ) hC2 N.act P.act Q.act
    N.finiteGeneration P.finiteGeneration Q.finiteGeneration x.2 y.2 z.2 φ ht (Complex.log (s : ℂ))
  rw [hchart.1,hchart.2,Complex.ofReal_add] at he
  have hl (γ : ℂ) : fivePointTerm hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (fiveEdge01 hC2 N P Q R).1) γ δ=
      φ (α.1 (pointTensorBlock hC2 T Q (Complex.log s) γ c δ
        (pointTensor hC2 N P (Complex.log r) x y γ) z)) := by
    let u := pointTensor hC2 N P (Complex.log r) x y γ
    let v := pointTensorBlock hC2 T Q (Complex.log s) γ c δ u z
    change f ((tensorMorphism hC2 α (𝟙 R)).1
      (pointTensorBlock hC2 L R 0 δ d β v w))=φ (α.1 v)
    rw [pointTensorBlock_map]
    exact (frozenPointFunctional_apply H.act R.act (tensorObject hC2 H R).act J 0 δ d β f
      ⟨α.1 v,hom_mem_weight L.act H.act (toWeakHom α) v.2⟩ w).symm
  have hr (γ : ℂ) : fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s f γ δ=
      φ (pointTensorBlock hC2 N S (Complex.log (s+r)) a γ δ x
        (pointTensor hC2 P Q (Complex.log s) y z γ)) := by
    exact (frozenPointFunctional_apply H.act R.act (tensorObject hC2 H R).act J 0 δ d β f _ w).symm
  rw [tsum_congr hl,tsum_congr hr]
  exact he.symm


-- Actual fixed-weight fourfold block types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The second true fiber is canonical block associativity with the genuine
second-third point component frozen as its middle input. -/
theorem fiberEdge12 (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .middle →ₗ[ℂ] ℂ) (γ : ℂ) :
    (∑' δ : ℂ,fivePointTerm hC2 N P Q R .inner a b c d β x y z w r s
      (f ∘ₗ (fiveEdge12 hC2 N P Q R).1) γ δ)=
    ∑' δ : ℂ,fivePointTerm hC2 N P Q R .middle a b c d β x y z w r s f γ δ := by
  let u := pointTensor hC2 P Q (Complex.log s) y z γ
  have hs : 0<s := hD.1.trans hD.2.1
  have he := associator_block_fiber hC2 N (tensorObject hC2 P Q) R a γ d β
    x u w (s+r) 1 (add_pos hs hD.1) one_pos (by linarith [hD.2.2]) f
  simp only [Complex.ofReal_one,Complex.log_one,Complex.ofReal_add,← add_assoc] at he
  simpa only [fivePointTerm,fiveEdge12,u] using he.symm

-- Actual fixed-weight fourfold block types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The left-to-pair fiber freezes the genuine first-second point component. -/
theorem fiberEdge04 (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .pair →ₗ[ℂ] ℂ) (γ : ℂ) :
    (∑' δ : ℂ,fivePointTerm hC2 N P Q R .left a b c d β x y z w r s
      (f ∘ₗ (fiveEdge04 hC2 N P Q R).1) γ δ)=
    ∑' δ : ℂ,fivePointTerm hC2 N P Q R .pair a b c d β x y z w r s f γ δ := by
  let u := pointTensor hC2 N P (Complex.log r) x y γ
  have hs : 0<s := hD.1.trans hD.2.1
  have he := associator_block_fiber hC2 (tensorObject hC2 N P) Q R γ c d β
    u z w s 1 hs one_pos (by linarith [hD.2.2,hD.1]) f
  simp only [Complex.ofReal_one,Complex.log_one] at he
  simpa only [fivePointTerm,fiveEdge04,u,pointTensor_eq_block hC2 Q R 0 c d] using he.symm

-- Actual fixed-weight fourfold block types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The pair-to-right fiber freezes the genuine last-two point component;
its fixed weight moves to the first internal index of the right tree. -/
theorem fiberEdge43 (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ) (δ : ℂ) :
    (∑' γ : ℂ,fivePointTerm hC2 N P Q R .pair a b c d β x y z w r s
      (f ∘ₗ (fiveEdge43 hC2 N P Q R).1) γ δ)=
    ∑' γ : ℂ,fivePointTerm hC2 N P Q R .right a b c d β x y z w r s f δ γ := by
  let u := pointTensor hC2 Q R 0 z w δ
  have hs : 0<s := hD.1.trans hD.2.1
  have he := associator_block_fiber hC2 N P (tensorObject hC2 Q R) a b δ β
    x y u r (1+s) hD.1 (by linarith) (by linarith [hD.2.1]) f
  simp only [Complex.ofReal_add,Complex.ofReal_one] at he
  simpa only [fivePointTerm,fiveEdge43,u,pointTensor_eq_block hC2 N P (Complex.log r) a b] using he.symm


-- Actual fixed-weight fourfold block types require a larger elaboration budget.
set_option maxHeartbeats 3000000 in
/-- The true middle-to-right fiber is the last-three associator paired
with the actual first-input frozen outer point block. -/
theorem fiberEdge23 (N P Q R : LogModuleCat W)
    (a b c d β : ℂ) (x : N.act.weight a) (y : P.act.weight b)
    (z : Q.act.weight c) (w : R.act.weight d) (r s : ℝ) (hD : FivePointDomain r s)
    (f : fivePointObject hC2 N P Q R .right →ₗ[ℂ] ℂ) (δ : ℂ) :
    (∑' γ : ℂ,fivePointTerm hC2 N P Q R .middle a b c d β x y z w r s
      (f ∘ₗ (fiveEdge23 hC2 N P Q R).1) γ δ)=
    ∑' γ : ℂ,fivePointTerm hC2 N P Q R .right a b c d β x y z w r s f γ δ := by
  let T := tensorObject hC2 P Q
  let L := tensorObject hC2 T R
  let S := tensorObject hC2 Q R
  let H := tensorObject hC2 P S
  let α := (associatorIso hC2 P Q R).hom
  let J := tensorIntertwiner hC2 N.act H.act N.finiteGeneration H.finiteGeneration
  let φ := frozenRightPointFunctional N.act H.act (tensorObject hC2 N H).act J
    (Complex.log (1+s+r)) a δ β f x
  have hs : 0<s := hD.1.trans hD.2.1
  have he := associator_block_fiber hC2 P Q R b c d δ y z w s 1 hs one_pos
    (by linarith [hD.2.2,hD.1]) φ
  simp only [Complex.ofReal_one,Complex.log_one] at he
  have hl (γ : ℂ) : fivePointTerm hC2 N P Q R .middle a b c d β x y z w r s
      (f ∘ₗ (fiveEdge23 hC2 N P Q R).1) γ δ=
      φ (α.1 (pointTensorBlock hC2 T R 0 γ d δ
        (pointTensor hC2 P Q (Complex.log s) y z γ) w)) := by
    let u := pointTensor hC2 P Q (Complex.log s) y z γ
    let v := pointTensorBlock hC2 T R 0 γ d δ u w
    change f ((tensorMorphism hC2 (𝟙 N) α).1
      (pointTensorBlock hC2 N L (Complex.log (1+s+r)) a δ β x v))=φ (α.1 v)
    rw [pointTensorBlock_map]
    exact (frozenRightPointFunctional_apply N.act H.act (tensorObject hC2 N H).act J
      (Complex.log (1+s+r)) a δ β f x ⟨α.1 v,hom_mem_weight L.act H.act (toWeakHom α) v.2⟩).symm
  have hr (γ : ℂ) : fivePointTerm hC2 N P Q R .right a b c d β x y z w r s f γ δ=
      φ (pointTensorBlock hC2 P S (Complex.log (1+s)) b γ δ y
        (pointTensor hC2 Q R 0 z w γ)) := by
    exact (frozenRightPointFunctional_apply N.act H.act (tensorObject hC2 N H).act J
      (Complex.log (1+s+r)) a δ β f x _).symm
  rw [tsum_congr hl,tsum_congr hr]
  simp_rw [pointTensor_eq_block hC2 P Q (Complex.log s) b c,
    pointTensor_eq_block hC2 Q R 0 c d]
  exact he.symm

end VOA.Huang.LogAssocFivePoint
