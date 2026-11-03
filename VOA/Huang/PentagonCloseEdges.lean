import VOA.Huang.TensorCatSewing
import VOA.Huang.TensorCatSpectrum

/-! # The single-weight pentagon edges for the evaluation associator

For the associator produced by `naturalReassociationOfEvaluation`, each of the
five single-weight edge identities of `FivePointFiberEdges` is one instance of
the defining four-point identity of the associator, after freezing the
unaffected internal weight into the test vector or into the output functional
and rescaling the real chart.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) (H : OrdinaryFourPointInput F)

/-- The associator family actually produced by the evaluation construction. -/
abbrev evalAssoc : AssociatorFamily F := (naturalReassociationOfEvaluation F H).associators

/-- The defining four-point identity of the evaluation associator. -/
theorem evalAssoc_fourPoint (X Y Z T : Ordinary W)
    (g : tensorObj F X (tensorObj F Y Z) ⟶ T) :
    iterateEvaluation F (postcompose (F (tensorObj F X Y) Z).intertwiner T.isMod
      ((evalAssoc F H X Y Z).hom ≫ g)) =
      productEvaluation F (postcompose (F X (tensorObj F Y Z)).intertwiner T.isMod g) := by
  let R := (naturalReassociationOfEvaluation F H).reassociation X Y Z
  have h1 := Reassociation.homEquiv_spec R T ((evalAssoc F H X Y Z).hom ≫ g)
  rw [Reassociation.homEquiv_eq_precompose] at h1
  change postcompose _ _ (R.associator.inv ≫ R.associator.hom ≫ g) = _ at h1
  rw [Iso.inv_hom_id_assoc] at h1
  exact (ordinaryFourPointCompare_spec F H X Y Z T _).symm.trans
    (congrArg (productEvaluation F) h1.symm)


omit [AddCommGroup V] [Module ℂ V] in
/-- Splitting a principal real power after rescaling. -/
theorem cpow_scale_split (c S : ℝ) (hc : 0 ≤ c) (hS : 0 < S) (A B : ℂ) :
    (((c * S : ℝ)) : ℂ) ^ A * (S : ℂ) ^ B = (c : ℂ) ^ A * (S : ℂ) ^ (A + B) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc hS.le, mul_assoc,
    ← Complex.cpow_add _ _ (by exact_mod_cast hS.ne')]

@[simp] theorem postcompose_val_apply {A B T N : Ordinary W}
    (I : IntertwiningOperator A.isMod B.isMod T.isMod) (f : T ⟶ N) (n : ℂ)
    (a : A.carrier) (b : B.carrier) :
    (postcompose I N.isMod f).val n a b = f.val (I.val n a b) := rfl

/-- Freezing the second input and the outer mode gives a functional supported
at the frozen internal weight. -/
theorem supportedAt_flip {A B N : Ordinary W} (I : IntertwiningOperator A.isMod B.isMod N.isMod)
    {φ : N.carrier →ₗ[ℂ] ℂ} {ε δ : ℂ} (hφ : SupportedAt N.isMod φ ε) {b : B.carrier}
    (hb : b ∈ B.isMod.weight δ) (v : ℂ) :
    SupportedAt A.isMod (φ ∘ₗ (I.val (v + δ - ε - 1)).flip b) v := by
  intro α hα u hu
  have hm := FusionTop.mem_weight I.property hu hb (v + δ - ε - 1)
  simp only [LinearMap.comp_apply, LinearMap.flip_apply]
  exact hφ _ (fun h => hα (by linear_combination h)) _ hm

/-- Freezing the first input and the outer mode. -/
theorem supportedAt_left {A B N : Ordinary W} (I : IntertwiningOperator A.isMod B.isMod N.isMod)
    {φ : N.carrier →ₗ[ℂ] ℂ} {ε α : ℂ} (hφ : SupportedAt N.isMod φ ε) {a : A.carrier}
    (ha : a ∈ A.isMod.weight α) (v : ℂ) :
    SupportedAt B.isMod (φ ∘ₗ I.val (α + v - ε - 1) a) v := by
  intro β hβ u hu
  have hm := FusionTop.mem_weight I.property ha hu (α + v - ε - 1)
  simp only [LinearMap.comp_apply]
  exact hφ _ (fun h => hβ (by linear_combination h)) _ hm

variable {X Y Z T U : Ordinary W}

theorem FivePointTest.s_pos (d : FivePointTest X Y Z T U) : 0 < d.s :=
  d.positive.trans d.smaller

theorem evalAssoc_edge01 (k : fiveObj F X Y Z T .inner ⟶ U) (d : FivePointTest X Y Z T U)
    (v : ℂ) :
    (∑' w : ℂ, fivePointTerm F .left (fiveEdge01 F X Y Z T (evalAssoc F H) ≫ k) d (w, v)) =
      ∑' w : ℂ, fivePointTerm F .inner k d (w, v) := by
  have hs := d.s_pos
  set c : ℝ := d.r / d.s with hc
  have hc0 : 0 < c := div_pos d.positive hs
  have hr : d.r = c * d.s := by rw [hc]; field_simp
  let d4 : FourPointTest X Y Z (tensorObj F X (tensorObj F Y Z)) :=
    { α := d.α, β := d.β, γ := d.γ, δ := v, x := d.x, y := d.y, z := d.z
      functional := d.functional ∘ₗ ((postcompose
        (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner U.isMod k).val
          (v + d.δ - d.ε - 1)).flip d.t
      hx := d.hx, hy := d.hy, hz := d.hz
      supported := supportedAt_flip _ d.supported d.ht v
      coordinate := c, positive := hc0
      less_one := by rw [hc, div_lt_one hs]; exact d.smaller }
  have h4 := congrFun (evalAssoc_fourPoint F H X Y Z _ (𝟙 _)) d4
  simp only [iterateEvaluation, productEvaluation] at h4
  have hl (w : ℂ) : fivePointTerm F .left (fiveEdge01 F X Y Z T (evalAssoc F H) ≫ k) d (w, v) =
      iterateWeightTerm F (postcompose (F (tensorObj F X Y) Z).intertwiner _
        ((evalAssoc F H X Y Z).hom ≫ 𝟙 _)) d4 w *
        (d.s : ℂ) ^ (v - d.α - d.β - d.γ) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, iterateWeightTerm,
      Ordinary.comp_apply, fiveEdge01, LinearMap.comp_apply, LinearMap.flip_apply, d4]
    rw [mul_assoc, hr, cpow_scale_split c d.s hc0.le hs]
    congr 1 <;> first | (congr 2; ring) | (erw [tensorHom_intertwiner]; rfl)
  have hrr (w : ℂ) : fivePointTerm F .inner k d (w, v) =
      productWeightTerm F (postcompose (F X (tensorObj F Y Z)).intertwiner _
        (𝟙 (tensorObj F X (tensorObj F Y Z)))) d4 w *
        (d.s : ℂ) ^ (v - d.α - d.β - d.γ) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, productWeightTerm,
      LinearMap.comp_apply, LinearMap.flip_apply, d4]
    have he : d.s + d.r = (1 + c) * d.s := by rw [hr]; ring
    rw [mul_assoc, he, mul_comm ((d.s : ℂ) ^ _), cpow_scale_split (1 + c) d.s (by linarith) hs]
    push_cast
    congr 1; congr 2; ring
  simp_rw [hl, hrr]
  rw [tsum_mul_right, tsum_mul_right, h4]


theorem evalAssoc_edge12 (k : fiveObj F X Y Z T .middle ⟶ U) (d : FivePointTest X Y Z T U)
    (w : ℂ) :
    (∑' v : ℂ, fivePointTerm F .inner (fiveEdge12 F X Y Z T (evalAssoc F H) ≫ k) d (w, v)) =
      ∑' v : ℂ, fivePointTerm F .middle k d (w, v) := by
  have hs := d.s_pos
  let d4 : FourPointTest X (tensorObj F Y Z) T U :=
    { α := d.α, β := w, γ := d.δ, δ := d.ε, x := d.x
      y := fiveFirstVector F .inner d w, z := d.t
      functional := d.functional
      hx := d.hx, hy := fiveFirstVector_mem F .inner d w, hz := d.ht
      supported := d.supported
      coordinate := d.s + d.r, positive := by linarith [d.positive]
      less_one := by linarith [d.sum_lt] }
  have h4 := congrFun (evalAssoc_fourPoint F H X (tensorObj F Y Z) T U k) d4
  simp only [iterateEvaluation, productEvaluation] at h4
  have hl (v : ℂ) : fivePointTerm F .inner (fiveEdge12 F X Y Z T (evalAssoc F H) ≫ k) d (w, v) =
      iterateWeightTerm F (postcompose (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner _
        ((evalAssoc F H X (tensorObj F Y Z) T).hom ≫ k)) d4 v *
        (d.s : ℂ) ^ (w - d.β - d.γ) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, iterateWeightTerm, d4]
    rw [mul_assoc, mul_comm ((d.s : ℂ) ^ _)]
    congr 1
  have hrr (v : ℂ) : fivePointTerm F .middle k d (w, v) =
      productWeightTerm F (postcompose (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner _ k)
        d4 v * (d.s : ℂ) ^ (w - d.β - d.γ) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, productWeightTerm, d4]
    rw [mul_assoc, mul_comm ((d.s : ℂ) ^ _)]
    push_cast
    congr 1; congr 2; ring
  simp_rw [hl, hrr]
  rw [tsum_mul_right, tsum_mul_right, h4]

theorem evalAssoc_edge23 (k : fiveObj F X Y Z T .right ⟶ U) (d : FivePointTest X Y Z T U)
    (v : ℂ) :
    (∑' w : ℂ, fivePointTerm F .middle (fiveEdge23 F X Y Z T (evalAssoc F H) ≫ k) d (w, v)) =
      ∑' w : ℂ, fivePointTerm F .right k d (w, v) := by
  have hs := d.s_pos
  let d4 : FourPointTest Y Z T (tensorObj F Y (tensorObj F Z T)) :=
    { α := d.β, β := d.γ, γ := d.δ, δ := v, x := d.y, y := d.z, z := d.t
      functional := d.functional ∘ₗ ((postcompose
        (F X (tensorObj F Y (tensorObj F Z T))).intertwiner U.isMod k).val
          (d.α + v - d.ε - 1)) d.x
      hx := d.hy, hy := d.hz, hz := d.ht
      supported := supportedAt_left _ d.supported d.hx v
      coordinate := d.s, positive := hs
      less_one := by linarith [d.sum_lt, d.positive] }
  have h4 := congrFun (evalAssoc_fourPoint F H Y Z T _ (𝟙 _)) d4
  simp only [iterateEvaluation, productEvaluation] at h4
  have hl (w : ℂ) : fivePointTerm F .middle (fiveEdge23 F X Y Z T (evalAssoc F H) ≫ k) d (w, v) =
      iterateWeightTerm F (postcompose (F (tensorObj F Y Z) T).intertwiner _
        ((evalAssoc F H Y Z T).hom ≫ 𝟙 (tensorObj F Y (tensorObj F Z T)))) d4 w *
        ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, iterateWeightTerm,
      Ordinary.comp_apply, fiveEdge23, LinearMap.comp_apply, d4]
    rw [mul_assoc]
    congr 1; erw [tensorHom_intertwiner]; rfl
  have hrr (w : ℂ) : fivePointTerm F .right k d (w, v) =
      productWeightTerm F (postcompose (F Y (tensorObj F Z T)).intertwiner _
        (𝟙 (tensorObj F Y (tensorObj F Z T)))) d4 w *
        ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, productWeightTerm,
      LinearMap.comp_apply, d4]
    rw [mul_assoc]
    push_cast
    congr 1
  simp_rw [hl, hrr]
  rw [tsum_mul_right, tsum_mul_right, h4]

theorem evalAssoc_edge04 (k : fiveObj F X Y Z T .pair ⟶ U) (d : FivePointTest X Y Z T U)
    (w : ℂ) :
    (∑' v : ℂ, fivePointTerm F .left (fiveEdge04 F X Y Z T (evalAssoc F H) ≫ k) d (w, v)) =
      ∑' v : ℂ, fivePointTerm F .pair k d (w, v) := by
  have hs := d.s_pos
  let d4 : FourPointTest (tensorObj F X Y) Z T U :=
    { α := w, β := d.γ, γ := d.δ, δ := d.ε, x := fiveFirstVector F .left d w
      y := d.z, z := d.t
      functional := d.functional
      hx := fiveFirstVector_mem F .left d w, hy := d.hz, hz := d.ht
      supported := d.supported
      coordinate := d.s, positive := hs
      less_one := by linarith [d.sum_lt, d.positive] }
  have h4 := congrFun (evalAssoc_fourPoint F H (tensorObj F X Y) Z T U k) d4
  simp only [iterateEvaluation, productEvaluation] at h4
  have hl (v : ℂ) : fivePointTerm F .left (fiveEdge04 F X Y Z T (evalAssoc F H) ≫ k) d (w, v) =
      iterateWeightTerm F (postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner _
        ((evalAssoc F H (tensorObj F X Y) Z T).hom ≫ k)) d4 v *
        (d.r : ℂ) ^ (w - d.α - d.β) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, iterateWeightTerm, d4]
    rw [mul_assoc, mul_comm ((d.r : ℂ) ^ _)]
    congr 1
  have hrr (v : ℂ) : fivePointTerm F .pair k d (w, v) =
      productWeightTerm F (postcompose (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner _ k)
        d4 v * (d.r : ℂ) ^ (w - d.α - d.β) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, productWeightTerm, d4]
    rw [mul_assoc, mul_comm ((d.r : ℂ) ^ _)]
    push_cast
    congr 1
  simp_rw [hl, hrr]
  rw [tsum_mul_right, tsum_mul_right, h4]

theorem evalAssoc_edge43 (k : fiveObj F X Y Z T .right ⟶ U) (d : FivePointTest X Y Z T U)
    (v : ℂ) :
    (∑' w : ℂ, fivePointTerm F .pair (fiveEdge43 F X Y Z T (evalAssoc F H) ≫ k) d (w, v)) =
      ∑' w : ℂ, fivePointTerm F .right k d (v, w) := by
  have hs := d.s_pos
  have hS : (0 : ℝ) < 1 + d.s := by linarith
  set c : ℝ := d.r / (1 + d.s) with hc
  have hc0 : 0 < c := div_pos d.positive hS
  have hr : d.r = c * (1 + d.s) := by rw [hc]; field_simp
  let d4 : FourPointTest X Y (tensorObj F Z T) U :=
    { α := d.α, β := d.β, γ := v, δ := d.ε, x := d.x, y := d.y
      z := fiveSecondVector F .pair d 0 v
      functional := d.functional
      hx := d.hx, hy := d.hy, hz := fiveSecondVector_mem F .pair d 0 v
      supported := d.supported
      coordinate := c, positive := hc0
      less_one := by rw [hc, div_lt_one hS]; linarith [d.smaller] }
  have h4 := congrFun (evalAssoc_fourPoint F H X Y (tensorObj F Z T) U k) d4
  simp only [iterateEvaluation, productEvaluation] at h4
  have hl (w : ℂ) : fivePointTerm F .pair (fiveEdge43 F X Y Z T (evalAssoc F H) ≫ k) d (w, v) =
      iterateWeightTerm F (postcompose (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner _
        ((evalAssoc F H X Y (tensorObj F Z T)).hom ≫ k)) d4 w *
        (((1 + d.s : ℝ)) : ℂ) ^ (d.ε - d.α - d.β - v) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, iterateWeightTerm, d4]
    rw [mul_assoc, hr, cpow_scale_split c (1 + d.s) hc0.le hS]
    congr 1; congr 2; ring
  have hrr (w : ℂ) : fivePointTerm F .right k d (v, w) =
      productWeightTerm F (postcompose (F X (tensorObj F Y (tensorObj F Z T))).intertwiner _ k)
        d4 w * (((1 + d.s : ℝ)) : ℂ) ^ (d.ε - d.α - d.β - v) := by
    simp only [fivePointTerm, fivePointVector, fivePointFactor, productWeightTerm, d4]
    have he : 1 + d.s + d.r = (1 + c) * (1 + d.s) := by rw [hr]; ring
    rw [mul_assoc, he, mul_comm (((1 + d.s : ℝ) : ℂ) ^ _),
      cpow_scale_split (1 + c) (1 + d.s) (by linarith) hS]
    push_cast
    congr 1; congr 2; ring
  simp_rw [hl, hrr]
  rw [tsum_mul_right, tsum_mul_right, h4]

/-- **All five single-weight pentagon edges hold** for the associator produced by
the evaluation construction, for any ordinary four-point input. -/
theorem evalAssoc_fiberEdges : FivePointFiberEdges F (evalAssoc F H) where
  edge01 _ _ _ _ _ k d v := evalAssoc_edge01 F H k d v
  edge12 _ _ _ _ _ k d w := evalAssoc_edge12 F H k d w
  edge23 _ _ _ _ _ k d v := evalAssoc_edge23 F H k d v
  edge04 _ _ _ _ _ k d w := evalAssoc_edge04 F H k d w
  edge43 _ _ _ _ _ k d v := evalAssoc_edge43 F H k d v

/-- The strongly rational instance: the associator of `monoidalCategoryOfStronglyRationalSewing`. -/
theorem fivePointFiberEdges_pbw (hV : StronglyRational W) :
    FivePointFiberEdges F
      (naturalReassociationOfEvaluation F (ordinaryFourPointInput_pbw F hV)).associators :=
  evalAssoc_fiberEdges F (ordinaryFourPointInput_pbw F hV)

end VOA.Huang.TensorCat
