import VOA.Huang.TensorCatVacuum

/-! # A concrete five-point sewing target

All five bracketings are evaluated at the same positive real configuration:
the four input points are `1+s+t`, `1+s`, `1`, `0`, with `0<t<s`
and `s+t<1`. Powers are principal powers of positive real numbers. Each
expression is the actual double sum of three universal intertwiner modes,
paired with a supported output functional.

The remaining analytic input asserts absolute convergence, coefficient
uniqueness, and compatibility of each individual four-point edge inside this
five-point function. It does not assert equality of the two pentagon paths.
The latter is proved here. Proving the edge input requires justified sum
interchanges and the four-point comparison; it is not supplied merely by
the existence of `AssociativityBoth`.

Sources: HLZ VI (arXiv:1012.4202), Sections 9--10, for the convergent
associativity comparison; HLZ VIII (arXiv:1110.1931), Section 12, for its
five-point use in coherence. Huang 2005, math/0303049, uses the corresponding
genus-zero associativity/duality in the genus-one construction. No genus-one
sewing estimate is assumed or proved in this file.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- The five vertices of the four-input associativity pentagon. -/
inductive FiveTree
  | left | inner | middle | right | pair
  deriving DecidableEq

/-- A common real sewing chart, with all vectors homogeneous. -/
structure FivePointTest (X Y Z T U : Ordinary W) where
  α : ℂ
  β : ℂ
  γ : ℂ
  δ : ℂ
  ε : ℂ
  x : X.carrier
  y : Y.carrier
  z : Z.carrier
  t : T.carrier
  functional : U.carrier →ₗ[ℂ] ℂ
  hx : x ∈ X.isMod.weight α
  hy : y ∈ Y.isMod.weight β
  hz : z ∈ Z.isMod.weight γ
  ht : t ∈ T.isMod.weight δ
  supported : SupportedAt U.isMod functional ε
  s : ℝ
  r : ℝ
  positive : 0 < r
  smaller : r < s
  sum_lt : s + r < 1

variable (F : FusionChoice W) (X Y Z T : Ordinary W)

/-- The actual tensor object at each pentagon vertex. -/
def fiveObj : FiveTree → Ordinary W
  | .left => tensorObj F (tensorObj F (tensorObj F X Y) Z) T
  | .inner => tensorObj F (tensorObj F X (tensorObj F Y Z)) T
  | .middle => tensorObj F X (tensorObj F (tensorObj F Y Z) T)
  | .right => tensorObj F X (tensorObj F Y (tensorObj F Z T))
  | .pair => tensorObj F (tensorObj F X Y) (tensorObj F Z T)

variable {X Y Z T} {U : Ordinary W}

/-- The unsummed, vector-valued coefficient at a specified pair of internal weights. -/
def fivePointVector (b : FiveTree) (d : FivePointTest X Y Z T U) (w : ℂ × ℂ) :
    (fiveObj F X Y Z T b).carrier :=
  match b with
  | .left =>
    (F (tensorObj F (tensorObj F X Y) Z) T).intertwiner.val (w.2 + d.δ - d.ε - 1)
      ((F (tensorObj F X Y) Z).intertwiner.val (w.1 + d.γ - w.2 - 1)
        ((F X Y).intertwiner.val (d.α + d.β - w.1 - 1) d.x d.y) d.z) d.t
  | .inner =>
    (F (tensorObj F X (tensorObj F Y Z)) T).intertwiner.val (w.2 + d.δ - d.ε - 1)
      ((F X (tensorObj F Y Z)).intertwiner.val (d.α + w.1 - w.2 - 1) d.x
        ((F Y Z).intertwiner.val (d.β + d.γ - w.1 - 1) d.y d.z)) d.t
  | .middle =>
    (F X (tensorObj F (tensorObj F Y Z) T)).intertwiner.val (d.α + w.2 - d.ε - 1) d.x
      ((F (tensorObj F Y Z) T).intertwiner.val (w.1 + d.δ - w.2 - 1)
        ((F Y Z).intertwiner.val (d.β + d.γ - w.1 - 1) d.y d.z) d.t)
  | .right =>
    (F X (tensorObj F Y (tensorObj F Z T))).intertwiner.val (d.α + w.2 - d.ε - 1) d.x
      ((F Y (tensorObj F Z T)).intertwiner.val (d.β + w.1 - w.2 - 1) d.y
        ((F Z T).intertwiner.val (d.γ + d.δ - w.1 - 1) d.z d.t))
  | .pair =>
    (F (tensorObj F X Y) (tensorObj F Z T)).intertwiner.val (w.1 + w.2 - d.ε - 1)
      ((F X Y).intertwiner.val (d.α + d.β - w.1 - 1) d.x d.y)
      ((F Z T).intertwiner.val (d.γ + d.δ - w.2 - 1) d.z d.t)

/-- The coordinate monomial. Powers at coordinate `1` have been removed. -/
def fivePointFactor (b : FiveTree) (d : FivePointTest X Y Z T U) (w : ℂ × ℂ) : ℂ :=
  match b with
  | .left => (d.r : ℂ) ^ (w.1 - d.α - d.β) * (d.s : ℂ) ^ (w.2 - w.1 - d.γ)
  | .inner => (d.s : ℂ) ^ (w.1 - d.β - d.γ) *
      ((d.s + d.r : ℝ) : ℂ) ^ (w.2 - d.α - w.1)
  | .middle => (d.s : ℂ) ^ (w.1 - d.β - d.γ) *
      ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - w.2)
  | .right => ((1 + d.s : ℝ) : ℂ) ^ (w.2 - d.β - w.1) *
      ((1 + d.s + d.r : ℝ) : ℂ) ^ (d.ε - d.α - w.2)
  | .pair => (d.r : ℂ) ^ (w.1 - d.α - d.β) *
      ((1 + d.s : ℝ) : ℂ) ^ (d.ε - w.1 - w.2)

/-- A scalar coefficient of three intertwiners after a module output map. -/
def fivePointTerm (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) (w : ℂ × ℂ) : ℂ :=
  d.functional (k.val (fivePointVector F b d w)) * fivePointFactor b d w

/-- Actual scalar five-point function; convergence remains an explicit obligation. -/
def fivePointEvaluation (b : FiveTree) (k : fiveObj F X Y Z T b ⟶ U)
    (d : FivePointTest X Y Z T U) : ℂ := ∑' w : ℂ × ℂ, fivePointTerm F b k d w

variable (a : AssociatorFamily F) (X Y Z T)

def fiveEdge01 : fiveObj F X Y Z T .left ⟶ fiveObj F X Y Z T .inner :=
  tensorHom F (a X Y Z).hom (𝟙 T)

def fiveEdge12 : fiveObj F X Y Z T .inner ⟶ fiveObj F X Y Z T .middle :=
  (a X (tensorObj F Y Z) T).hom

def fiveEdge23 : fiveObj F X Y Z T .middle ⟶ fiveObj F X Y Z T .right :=
  tensorHom F (𝟙 X) (a Y Z T).hom

def fiveEdge04 : fiveObj F X Y Z T .left ⟶ fiveObj F X Y Z T .pair :=
  (a (tensorObj F X Y) Z T).hom

def fiveEdge43 : fiveObj F X Y Z T .pair ⟶ fiveObj F X Y Z T .right :=
  (a X Y (tensorObj F Z T)).hom

/-- Each single four-point reassociation is valid inside the common five-point
function. True for the analytically normalized associator under Huang/HLZ
hypotheses; not asserted for arbitrary isomorphism families. No path equality
is included. Each field still needs an analytic sewing proof. -/
structure FivePointEdges : Prop where
  edge01 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .inner ⟶ U) :
    fivePointEvaluation F .left (fiveEdge01 F X Y Z T a ≫ k) =
      fivePointEvaluation F .inner k
  edge12 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .middle ⟶ U) :
    fivePointEvaluation F .inner (fiveEdge12 F X Y Z T a ≫ k) =
      fivePointEvaluation F .middle k
  edge23 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .right ⟶ U) :
    fivePointEvaluation F .middle (fiveEdge23 F X Y Z T a ≫ k) =
      fivePointEvaluation F .right k
  edge04 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .pair ⟶ U) :
    fivePointEvaluation F .left (fiveEdge04 F X Y Z T a ≫ k) =
      fivePointEvaluation F .pair k
  edge43 (X Y Z T U : Ordinary W) (k : fiveObj F X Y Z T .right ⟶ U) :
    fivePointEvaluation F .pair (fiveEdge43 F X Y Z T a ≫ k) =
      fivePointEvaluation F .right k

/-- The five-point expansion/uniqueness obligations on the explicit common
chart. This retains absolute convergence rather than treating total `tsum`
as an analytic existence theorem. -/
structure FivePointSewingInput : Prop where
  summability (X Y Z T U : Ordinary W) (b : FiveTree)
    (k : fiveObj F X Y Z T b ⟶ U) (d : FivePointTest X Y Z T U) :
    Summable (fivePointTerm F b k d)
  faithful (X Y Z T U : Ordinary W) :
    Function.Injective (fivePointEvaluation F (X := X) (Y := Y) (Z := Z) (T := T) (U := U) .left)
  edges : FivePointEdges F a

/-- The two pentagon paths agree after scalar evaluation: three individual
edges on the long path, two on the short path. -/
theorem pentagon_evaluation_eq (he : FivePointEdges F a) :
    fivePointEvaluation F .left (pentagonLong F a X Y Z T) =
      fivePointEvaluation F .left (pentagonShort F a X Y Z T) := by
  let U := fiveObj F X Y Z T .right
  have h23 := he.edge23 X Y Z T U (𝟙 U)
  have h43 := he.edge43 X Y Z T U (𝟙 U)
  change fivePointEvaluation F .middle (fiveEdge23 F X Y Z T a) =
    fivePointEvaluation F .right (𝟙 U) at h23
  change fivePointEvaluation F .pair (fiveEdge43 F X Y Z T a) =
    fivePointEvaluation F .right (𝟙 U) at h43
  change fivePointEvaluation F .left
    (fiveEdge01 F X Y Z T a ≫ fiveEdge12 F X Y Z T a ≫ fiveEdge23 F X Y Z T a) =
      fivePointEvaluation F .left (fiveEdge04 F X Y Z T a ≫ fiveEdge43 F X Y Z T a)
  rw [he.edge01, he.edge12, h23, he.edge04, h43]

/-- Five-point uniqueness upgrades the analytic path calculation to mode coherence. -/
theorem pentagonOnModes_of_fivePointSewing (hs : FivePointSewingInput F a) :
    PentagonOnModes F a := by
  intro X Y Z T p q r x y z t
  have he := hs.faithful X Y Z T (fiveObj F X Y Z T .right)
    (pentagon_evaluation_eq F X Y Z T a hs.edges)
  exact congrArg (fun f => f.val (fourfoldMode F X Y Z T p q r x y z t)) he

/-- Conditional assembly with input naturality proved by representability,
the triangle reduced to creation, and the pentagon reduced to explicit sewing. -/
abbrev monoidalCategoryOfEvaluation (H : OrdinaryFourPointInput F)
    (hs : FivePointSewingInput F (naturalReassociationOfEvaluation F H).associators)
    (hv : VacuumCreationCompatibility F (naturalReassociationOfEvaluation F H).associators) :
    MonoidalCategory (Ordinary W) :=
  monoidalCategoryOfModes F (naturalReassociationOfEvaluation F H).associators
    (naturalReassociationOfEvaluation F H).associator_naturality
    (pentagonOnModes_of_fivePointSewing F _ hs)
    (triangleOnModes_of_vacuumCreation F _ hv)

end VOA.Huang.TensorCat
