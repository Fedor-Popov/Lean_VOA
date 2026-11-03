import VOA.Huang.TensorCatSlices

/-! # Finite spectral support for the actual five-point double sums

The two internal weights lie in finite unions of lowest-weight progressions.
This does not assert convergence, but discharges the reindexing/support part
of applying a two-index analytic estimate, including repeated lowest weights.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- An actual finite presentation bounds the entire weight spectrum. -/
theorem SimplePresentation.weight_mem {X : Ordinary W} (P : SimplePresentation X)
    {w : ℂ} (hw : X.isMod.weight w ≠ ⊥) :
    ∃ j : Fin P.size, ∃ n : ℕ, w = (P.part j).h + n := by
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hn : ∃ j, (P.proj j).val x ≠ 0 := by
    by_contra hh
    push Not at hh
    have ht := P.total x
    simp only [hh, map_zero, Finset.sum_const_zero] at ht
    exact hx₀ ht.symm
  obtain ⟨j, hj⟩ := hn
  have hm := hom_mem_weight (P.proj j).property hx
  change (P.proj j).val x ∈ (P.part j).isMod.weight w at hm
  obtain ⟨n, he⟩ := (P.part j).isLow w (fun hz => hj (by
    rw [hz] at hm
    change (P.proj j).val x = 0 at hm
    exact hm))
  exact ⟨j, n, he⟩

/-- A finite union of progressions supports every ordinary module. -/
theorem finite_weight_spectrum (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (X : Ordinary W) :
    ∃ S : Finset ℂ, ∀ w, X.isMod.weight w ≠ ⊥ → ∃ h ∈ S, ∃ n : ℕ, w = h + n := by
  obtain ⟨P⟩ := simplePresentation_nonempty hV hΦ X
  refine ⟨Finset.univ.image (fun j => (P.part j).h), fun w hw => ?_⟩
  obtain ⟨j, n, hn⟩ := P.weight_mem hw
  exact ⟨(P.part j).h, Finset.mem_image_of_mem _ (Finset.mem_univ j), n, hn⟩

variable (F : FusionChoice W) (X Y Z T : Ordinary W)

/-- The module carrying the first internal weight in the fixed five-point convention. -/
def fiveFirstObj : FiveTree → Ordinary W
  | .left | .pair => tensorObj F X Y
  | .inner | .middle => tensorObj F Y Z
  | .right => tensorObj F Z T

/-- The module carrying the second internal weight. -/
def fiveSecondObj : FiveTree → Ordinary W
  | .left => tensorObj F (tensorObj F X Y) Z
  | .inner => tensorObj F X (tensorObj F Y Z)
  | .middle => tensorObj F (tensorObj F Y Z) T
  | .right => tensorObj F Y (tensorObj F Z T)
  | .pair => tensorObj F Z T

variable {X Y Z T} {U : Ordinary W}

def fiveFirstVector (b : FiveTree) (d : FivePointTest X Y Z T U) (w : ℂ) :
    (fiveFirstObj F X Y Z T b).carrier :=
  match b with
  | .left | .pair => (F X Y).intertwiner.val (d.α + d.β - w - 1) d.x d.y
  | .inner | .middle => (F Y Z).intertwiner.val (d.β + d.γ - w - 1) d.y d.z
  | .right => (F Z T).intertwiner.val (d.γ + d.δ - w - 1) d.z d.t

def fiveSecondVector (b : FiveTree) (d : FivePointTest X Y Z T U) (w v : ℂ) :
    (fiveSecondObj F X Y Z T b).carrier :=
  match b with
  | .left => (F (tensorObj F X Y) Z).intertwiner.val (w + d.γ - v - 1)
      (fiveFirstVector F .left d w) d.z
  | .inner => (F X (tensorObj F Y Z)).intertwiner.val (d.α + w - v - 1)
      d.x (fiveFirstVector F .inner d w)
  | .middle => (F (tensorObj F Y Z) T).intertwiner.val (w + d.δ - v - 1)
      (fiveFirstVector F .middle d w) d.t
  | .right => (F Y (tensorObj F Z T)).intertwiner.val (d.β + w - v - 1)
      d.y (fiveFirstVector F .right d w)
  | .pair => (F Z T).intertwiner.val (d.γ + d.δ - v - 1) d.z d.t

private theorem level_mode_mem {X Y : Ordinary W} (P : Product X.isMod Y.isMod)
    {α β : ℂ} {x : X.carrier} {y : Y.carrier}
    (hx : x ∈ X.isMod.weight α) (hy : y ∈ Y.isMod.weight β) (w : ℂ) :
    P.intertwiner.val (α + β - w - 1) x y ∈ P.isMod.weight w := by
  have h := FusionTop.mem_weight P.intertwiner.property hx hy (α + β - w - 1)
  convert h using 1
  congr 1
  ring

/-- Both explicit internal vectors have their stated internal weights. -/
theorem fiveFirstVector_mem (b : FiveTree) (d : FivePointTest X Y Z T U) (w : ℂ) :
    fiveFirstVector F b d w ∈ (fiveFirstObj F X Y Z T b).isMod.weight w := by
  cases b with
  | left | pair => exact level_mode_mem (F X Y) d.hx d.hy w
  | inner | middle => exact level_mode_mem (F Y Z) d.hy d.hz w
  | right => exact level_mode_mem (F Z T) d.hz d.ht w

theorem fiveSecondVector_mem (b : FiveTree) (d : FivePointTest X Y Z T U) (w v : ℂ) :
    fiveSecondVector F b d w v ∈ (fiveSecondObj F X Y Z T b).isMod.weight v := by
  cases b with
  | left => exact level_mode_mem (F (tensorObj F X Y) Z) (fiveFirstVector_mem F .left d w) d.hz v
  | inner => exact level_mode_mem (F X (tensorObj F Y Z)) d.hx (fiveFirstVector_mem F .inner d w) v
  | middle =>
    exact level_mode_mem (F (tensorObj F Y Z) T) (fiveFirstVector_mem F .middle d w) d.ht v
  | right => exact level_mode_mem (F Y (tensorObj F Z T)) d.hy (fiveFirstVector_mem F .right d w) v
  | pair => exact level_mode_mem (F Z T) d.hz d.ht v

/-- A nonzero five-point coefficient forces both internal weight spaces to be nonzero. -/
theorem fivePointTerm_weight_support (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (w v : ℂ)
    (hne : fivePointTerm F b k d (w, v) ≠ 0) :
    (fiveFirstObj F X Y Z T b).isMod.weight w ≠ ⊥ ∧
      (fiveSecondObj F X Y Z T b).isMod.weight v ≠ ⊥ := by
  constructor
  · intro hz
    have hv := fiveFirstVector_mem F b d w
    rw [hz, Submodule.mem_bot] at hv
    apply hne
    clear hne
    cases b <;> simp only [fiveFirstVector] at hv <;>
      simp only [fivePointTerm, fivePointVector, hv] <;>
      (repeat' first | erw [LinearMap.map_zero₂] | erw [map_zero] | rw [zero_mul])
  · intro hz
    have hv := fiveSecondVector_mem F b d w v
    rw [hz, Submodule.mem_bot] at hv
    apply hne
    clear hne
    cases b <;> simp only [fiveSecondVector, fiveFirstVector] at hv <;>
      simp only [fivePointTerm, fivePointVector, hv] <;>
      (repeat' first | erw [LinearMap.map_zero₂] | erw [map_zero] | rw [zero_mul])

/-- The full scalar double sum has a finite rectangular spectral cover. -/
theorem fivePoint_finite_spectral_cover (hV : StronglyRational W) (hΦ : Finite (Φ W))
    (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U) (d : FivePointTest X Y Z T U) :
    ∃ S T : Finset ℂ, ∀ w v, fivePointTerm F b k d (w, v) ≠ 0 →
      ∃ h ∈ S, ∃ h' ∈ T, ∃ m n : ℕ, w = h + m ∧ v = h' + n := by
  obtain ⟨S, hS⟩ := finite_weight_spectrum hV hΦ (fiveFirstObj F X Y Z T b)
  obtain ⟨T, hT⟩ := finite_weight_spectrum hV hΦ (fiveSecondObj F X Y Z T b)
  refine ⟨S, T, fun w v hne => ?_⟩
  obtain ⟨hw, hv⟩ := fivePointTerm_weight_support F b k d w v hne
  obtain ⟨h, hh, m, hm⟩ := hS w hw
  obtain ⟨h', hh', n, hn⟩ := hT v hv
  exact ⟨h, hh, h', hh', m, n, hm, hn⟩

end VOA.Huang.TensorCat
