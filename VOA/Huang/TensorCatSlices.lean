import VOA.Huang.TensorCatSewing

/-! # Convergence of individual five-point slices

Four-point convergence proves each fixed-internal-weight slice converges.
The outstanding joint estimate is summability of these slice norms over the
other internal weight. No interchange is made without that estimate.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
variable (F : FusionChoice W) {X Y Z T U : Ordinary W}

/-- Freeze the X--Y intermediate coefficient. -/
def FivePointTest.leftSlice (d : FivePointTest X Y Z T U) (w : ℂ) :
    FourPointTest (tensorObj F X Y) Z T U where
  α := w
  β := d.γ
  γ := d.δ
  δ := d.ε
  x := (F X Y).intertwiner.val (d.α + d.β - w - 1) d.x d.y
  y := d.z
  z := d.t
  functional := d.functional
  hx := by
    have h := FusionTop.mem_weight (F X Y).intertwiner.property d.hx d.hy
      (d.α + d.β - w - 1)
    convert h using 1
    congr 1
    ring
  hy := d.hz
  hz := d.ht
  supported := d.supported
  coordinate := d.s
  positive := lt_trans d.positive d.smaller
  less_one := by linarith [d.sum_lt, d.positive]

/-- Freeze the Y--Z intermediate coefficient. -/
def FivePointTest.innerSlice (d : FivePointTest X Y Z T U) (w : ℂ) :
    FourPointTest X (tensorObj F Y Z) T U where
  α := d.α
  β := w
  γ := d.δ
  δ := d.ε
  x := d.x
  y := (F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z
  z := d.t
  functional := d.functional
  hx := d.hx
  hy := by
    have h := FusionTop.mem_weight (F Y Z).intertwiner.property d.hy d.hz
      (d.β + d.γ - w - 1)
    convert h using 1
    congr 1
    ring
  hz := d.ht
  supported := d.supported
  coordinate := d.s + d.r
  positive := by linarith [d.positive, d.smaller]
  less_one := d.sum_lt

/-- Freeze the Z--T coefficient and rescale the remaining two coordinates. -/
def FivePointTest.rightSlice (d : FivePointTest X Y Z T U) (w : ℂ) :
    FourPointTest X Y (tensorObj F Z T) U where
  α := d.α
  β := d.β
  γ := w
  δ := d.ε
  x := d.x
  y := d.y
  z := (F Z T).intertwiner.val (d.γ + d.δ - w - 1) d.z d.t
  functional := d.functional
  hx := d.hx
  hy := d.hy
  hz := by
    have h := FusionTop.mem_weight (F Z T).intertwiner.property d.hz d.ht
      (d.γ + d.δ - w - 1)
    convert h using 1
    congr 1
    ring
  supported := d.supported
  coordinate := d.r / (1 + d.s)
  positive := div_pos d.positive (by linarith [d.positive, d.smaller])
  less_one := (div_lt_one (by linarith [d.positive, d.smaller])).mpr
    (by linarith [d.smaller])

/-- The positive-real branch respects the coordinate rescaling used on the right tree. -/
theorem fivePoint_right_factor (d : FivePointTest X Y Z T U) (w v : ℂ) :
    fivePointFactor .right d (w, v) =
      (1 + ((d.r / (1 + d.s) : ℝ) : ℂ)) ^ (d.ε - d.α - v) *
        ((1 + d.s : ℝ) : ℂ) ^ (d.ε - d.α - d.β - w) := by
  have hb : 0 < 1 + d.s := by linarith [d.positive, d.smaller]
  have hc : 0 < 1 + d.r / (1 + d.s) := by
    have hr := d.positive
    positivity
  have he : 1 + d.s + d.r = (1 + d.s) * (1 + d.r / (1 + d.s)) := by
    field_simp
  change ((1 + d.s : ℝ) : ℂ) ^ (v - d.β - w) *
    ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - v) = _
  rw [he, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hb.le hc.le]
  rw [← mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast hb.ne')]
  rw [show (v - d.β - w) + (d.ε - d.α - v) = d.ε - d.α - d.β - w by ring]
  push_cast
  ring

/-- Every fixed first-weight slice is summable, for all five bracketings.
This proves the first clause of FivePointNormFibers from four-point convergence. -/
theorem fivePoint_slice_summable (hs : OrdinaryFourPointSummability F)
    (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (w : ℂ) :
    Summable (fun v : ℂ => fivePointTerm F b k d (w, v)) := by
  cases b with
  | left =>
    let I := postcompose (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner U.isMod k
    have hh := ((hs _ _ _ _ (d.leftSlice F w)).1 I).mul_right
      ((d.r : ℂ) ^ (w - d.α - d.β))
    apply hh.congr
    intro v
    change d.functional (k.val _) * (d.s : ℂ) ^ (v - w - d.γ) *
      (d.r : ℂ) ^ (w - d.α - d.β) = _
    dsimp only [fivePointTerm, fivePointVector, fivePointFactor, FivePointTest.leftSlice,
      FivePointTest.innerSlice, FivePointTest.rightSlice]
    ring
  | inner =>
    let I := postcompose (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner U.isMod k
    have hh := ((hs _ _ _ _ (d.innerSlice F w)).1 I).mul_right
      ((d.s : ℂ) ^ (w - d.β - d.γ))
    apply hh.congr
    intro v
    change d.functional (k.val _) * ((d.s + d.r : ℝ) : ℂ) ^ (v - d.α - w) *
      (d.s : ℂ) ^ (w - d.β - d.γ) = _
    dsimp only [fivePointTerm, fivePointVector, fivePointFactor, FivePointTest.leftSlice,
      FivePointTest.innerSlice, FivePointTest.rightSlice]
    ring
  | middle =>
    let I := postcompose (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner U.isMod k
    have hh := ((hs _ _ _ _ (d.innerSlice F w)).2 I).mul_right
      ((d.s : ℂ) ^ (w - d.β - d.γ))
    apply hh.congr
    intro v
    change d.functional (k.val _) * (1 + ((d.s + d.r : ℝ) : ℂ)) ^ (d.ε - d.α - v) *
      (d.s : ℂ) ^ (w - d.β - d.γ) = _
    dsimp only [fivePointTerm, fivePointVector, fivePointFactor, FivePointTest.leftSlice,
      FivePointTest.innerSlice, FivePointTest.rightSlice]
    rw [show (1 + ((d.s + d.r : ℝ) : ℂ)) = ((1 + d.s + d.r : ℝ) : ℂ) by push_cast; ring]
    ring
  | right =>
    let I := postcompose (F X (tensorObj F Y (tensorObj F Z T))).intertwiner U.isMod k
    have hh := ((hs _ _ _ _ (d.rightSlice F w)).2 I).mul_right
      (((1 + d.s : ℝ) : ℂ) ^ (d.ε - d.α - d.β - w))
    apply hh.congr
    intro v
    change d.functional (k.val _) * (1 + ((d.r / (1 + d.s) : ℝ) : ℂ)) ^ (d.ε - d.α - v) *
      ((1 + d.s : ℝ) : ℂ) ^ (d.ε - d.α - d.β - w) = _
    rw [fivePointTerm, fivePoint_right_factor]
    dsimp only [FivePointTest.rightSlice, fivePointVector]
    ring
  | pair =>
    let I := postcompose (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner U.isMod k
    have hh := ((hs _ _ _ _ (d.leftSlice F w)).2 I).mul_right
      ((d.r : ℂ) ^ (w - d.α - d.β))
    apply hh.congr
    intro v
    change d.functional (k.val _) * (1 + (d.s : ℂ)) ^ (d.ε - w - v) *
      (d.r : ℂ) ^ (w - d.α - d.β) = _
    dsimp only [fivePointTerm, fivePointVector, fivePointFactor, FivePointTest.leftSlice,
      FivePointTest.innerSlice, FivePointTest.rightSlice]
    push_cast
    ring

/-- Strong rationality supplies absolute convergence of each individual slice. -/
theorem fivePoint_slice_summable_pbw (hV : StronglyRational W)
    (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (w : ℂ) :
    Summable (fun v : ℂ => fivePointTerm F b k d (w, v)) :=
  fivePoint_slice_summable F (ordinaryFourPointSummability_pbw F hV) b k d w

/-- The still-open estimate after all the individual slices have been proved
absolutely convergent. Its domain and weights are the actual five-point chart. -/
def FivePointNormGrowth : Prop :=
  ∀ (X Y Z T U : Ordinary W) (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U),
    Summable (fun w : ℂ => ∑' v : ℂ, ‖fivePointTerm F b k d (w, v)‖)

/-- Under strong rationality only the summed norm estimate remains for joint convergence. -/
theorem fivePointSummability_iff_normGrowth_pbw (hV : StronglyRational W) :
    FivePointSummability F ↔ FivePointNormGrowth F := by
  rw [fivePointSummability_iff_normFibers]
  constructor
  · exact fun h X Y Z T U b k d => (h X Y Z T U b k d).2
  · intro h X Y Z T U b k d
    exact ⟨fun w => (fivePoint_slice_summable F (ordinaryFourPointSummability_pbw F hV)
      b k d w).norm, h X Y Z T U b k d⟩

/-- The remaining norm growth, left uniqueness, and single-weight edge identities
imply sewing; all four-point and individual-slice convergence inputs are discharged. -/
theorem fivePointSewingInput_of_normGrowth_pbw (hV : StronglyRational W)
    (a : AssociatorFamily F) (hg : FivePointNormGrowth F)
    (hf : FivePointLeftFaithfulness F) (he : FivePointFiberEdges F a) :
    FivePointSewingInput F a :=
  ⟨(fivePointSummability_iff_normGrowth_pbw F hV).mpr hg, hf,
    fivePointEdges_of_fibers F a ((fivePointSummability_iff_normGrowth_pbw F hV).mpr hg) he⟩

end VOA.Huang.TensorCat
