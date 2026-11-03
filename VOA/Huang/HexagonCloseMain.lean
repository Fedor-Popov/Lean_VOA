import VOA.Huang.HexagonCloseIterate

/-! # Hexagon closure: the hexagon as one analytic-continuation identity

`BraidRibbon.HexagonInput F` (the analytic hexagon for FHL's two phases, equivalent to the two
forward hexagons, `analyticHexagon_iff`) is reduced here, by proved evaluation formulas, to a
braiding-free statement about **iterate series at continued points** (`HexagonContinuation`):

for `K ∈ I((Y⊠Z)X;T)`, `M ∈ I((Y⊠X)Z;T)`, `G ∈ I(Y(Z⊠X);T)` with the real-segment identities
`It K = Pr G`, `It M = Pr(G ∘ (1 × c_{X,Z}))`, and every real test with `0 < r < 1/2`,

`e^{(α+β+γ-δ)κ} Σ_j ((-1)^j/j!) It_K(y,z,x; f∘L₋₁^j)(κ - log(1+r))
  = It_M(y,x,z; f)(log r - log(1+r) - κ)`

(`κ = -πi` for `Ω₀`, `κ = πi` for `Ω₋₁`).  Each side is an absolutely convergent series
(`summable_iterL`) of an iterate evaluated at a point **off** the real segment where the
hypotheses are known: `ρ_K = e^{κ}/(1+r)`, `ρ_M = e^{-κ} r/(1+r)`.  Proved:

* `analyticHexagon_of_continuation : HexagonContinuation F p κ → AnalyticHexagon F p`
  (product side `productEvaluation_skewP`, iterate side `iterateEvaluation_braid` for
  `r < 1/2`, then the identity theorem in the coordinate `iterate_eq_product_of_small`);
* `continuation_of_analyticHexagon` (converse), hence `hexagonContinuation_iff`: the
  continuation identity is **exactly** the analytic hexagon — true iff Huang's hexagon holds
  (hence TRUE for strongly rational `W`), and not vacuous;
* `hexagonInput_of_continuation`, `braidedCategory_of_continuation`.

What the continuation identity still needs (not proved here): the four-point function as one
holomorphic function along a path from the
`G`-product region through the `K`- and `M`-iterate regions; on the real configuration space the
two sides lie in different chambers of a six-cycle, and the closing step is the absence of
monodromy around the equilateral configuration `u = e^{±iπ/3}`, where none of the standard
iterate/product expansions converges.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff VOA.Huang.BraidingSkew
open Complex
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

open BraidRibbon

variable (F : FusionChoice W)

/-- **The hexagon as an analytic-continuation identity** for a phase `p` of exponential form
`p.c n = e^{κ(n+1)}`.  See the module docstring.  TRUE for strongly rational `W` and
`p ∈ {Phase.upper, Phase.upper.inv}` (it is equivalent to `AnalyticHexagon F p`,
`hexagonContinuation_iff`, i.e. to Huang's hexagon theorem). -/
def HexagonContinuation (p : Phase) (κ : ℂ) : Prop :=
  ∀ (X Y Z T : Ordinary W) (K : IterateSpace F Y Z X T) (M : IterateSpace F Y X Z T)
    (G : ProductSpace F Y Z X T),
    iterateEvaluation F K = productEvaluation F G →
    iterateEvaluation F M =
      productEvaluation F (restrictInputs (𝟙 Y) (braidingP p F X Z).hom G) →
    ∀ d : FourPointTest X Y Z T, d.coordinate < 1 / 2 →
      Complex.exp ((d.α + d.β + d.γ - d.δ) * κ) *
          ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (κ - Real.log (1 + d.coordinate)) =
        iterL F M d.swapM
          ((Real.log d.coordinate : ℂ) - Real.log (1 + d.coordinate) - κ)

/-- FHL's `Ω₀` has `κ = -πi`. -/
theorem phase_upper_exp (n : ℂ) :
    Phase.upper.c n = Complex.exp (-(↑Real.pi * Complex.I) * (n + 1)) := rfl

/-- FHL's `Ω₋₁` has `κ = πi`. -/
theorem phase_upper_inv_exp (n : ℂ) :
    Phase.upper.inv.c n = Complex.exp ((↑Real.pi * Complex.I) * (n + 1)) := by
  change (Complex.exp (-(↑Real.pi * Complex.I) * (n + 1)))⁻¹ = _
  rw [← Complex.exp_neg, neg_mul, neg_neg]

/-- The two continued sides, as the two hexagon evaluations (`r < 1/2`). -/
theorem hexagon_sides (hV : StronglyRational W) (p : Phase) {κ : ℂ}
    (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1))) {X Y Z T : Ordinary W}
    (K : IterateSpace F Y Z X T) (M : IterateSpace F Y X Z T) (d : FourPointTest X Y Z T)
    (hr : d.coordinate < 1 / 2) :
    (productEvaluation F (skewP p (tensorObj F Y Z) X T K) d =
        iterateEvaluation F (restrictInputs (braidingP p F X Y).hom (𝟙 Z) M) d) ↔
      Complex.exp ((d.α + d.β + d.γ - d.δ) * κ) *
          ∑' j : ℕ, sc j * iterL F K (d.lowerK j) (κ - Real.log (1 + d.coordinate)) =
        iterL F M d.swapM
          ((Real.log d.coordinate : ℂ) - Real.log (1 + d.coordinate) - κ) := by
  rw [productEvaluation_skewP F hV p hκ K d, iterateEvaluation_braid F hV p hκ M d hr]
  set E := Complex.exp ((d.δ - d.α - d.β - d.γ) * Real.log (1 + d.coordinate)) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hsplit : Complex.exp ((d.δ - d.α - d.β - d.γ) *
      ((Real.log (1 + d.coordinate) : ℂ) - κ)) =
      E * Complex.exp ((d.α + d.β + d.γ - d.δ) * κ) := by
    rw [hE, ← Complex.exp_add]; congr 1; ring
  rw [hsplit, mul_assoc]
  exact ⟨fun h => mul_left_cancel₀ hE0 h, fun h => by rw [h]⟩

/-- **The continuation identity gives the analytic hexagon.** -/
theorem analyticHexagon_of_continuation (hV : StronglyRational W) (p : Phase) {κ : ℂ}
    (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1))) (h : HexagonContinuation F p κ) :
    AnalyticHexagon F p := by
  intro X Y Z T K M G hK hM
  funext d
  refine (iterate_eq_product_of_small F hV _ _ d (ε := 1 / 2) (by norm_num)
    (fun r h0 h1 hr => ?_)).symm
  have hd : (d.withCoord r h0 h1).coordinate < 1 / 2 := hr
  exact ((hexagon_sides F hV p hκ K M (d.withCoord r h0 h1) hd).2
    (h X Y Z T K M G hK hM (d.withCoord r h0 h1) hd)).symm

/-- **Converse**: the analytic hexagon gives the continuation identity. -/
theorem continuation_of_analyticHexagon (hV : StronglyRational W) (p : Phase) {κ : ℂ}
    (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1))) (h : AnalyticHexagon F p) :
    HexagonContinuation F p κ := by
  intro X Y Z T K M G hK hM d hr
  exact (hexagon_sides F hV p hκ K M d hr).1 (congrFun (h X Y Z T K M G hK hM) d)

/-- The continuation identity is exactly the analytic hexagon (strongly rational `W`). -/
theorem hexagonContinuation_iff (hV : StronglyRational W) (p : Phase) {κ : ℂ}
    (hκ : ∀ n, p.c n = Complex.exp (κ * (n + 1))) :
    HexagonContinuation F p κ ↔ AnalyticHexagon F p :=
  ⟨analyticHexagon_of_continuation F hV p hκ, continuation_of_analyticHexagon F hV p hκ⟩

/-- **The continuation input**: the identity for FHL's two phases `Ω₀` (`κ = -πi`) and `Ω₋₁`
(`κ = πi`).  TRUE for strongly rational `W` (Huang's hexagon theorem), equivalent to
`HexagonInput F` (`hexagonContinuationInput_iff`). -/
def HexagonContinuationInput : Prop :=
  HexagonContinuation F Phase.upper (-(↑Real.pi * Complex.I)) ∧
    HexagonContinuation F Phase.upper.inv (↑Real.pi * Complex.I)

/-- **The hexagon input from the continuation input.** -/
theorem hexagonInput_of_continuation (hV : StronglyRational W)
    (h : HexagonContinuationInput F) : HexagonInput F :=
  ⟨analyticHexagon_of_continuation F hV Phase.upper phase_upper_exp h.1,
    analyticHexagon_of_continuation F hV Phase.upper.inv phase_upper_inv_exp h.2⟩

theorem hexagonContinuationInput_iff (hV : StronglyRational W) :
    HexagonContinuationInput F ↔ HexagonInput F :=
  ⟨hexagonInput_of_continuation F hV, fun h =>
    ⟨continuation_of_analyticHexagon F hV Phase.upper phase_upper_exp h.1,
      continuation_of_analyticHexagon F hV Phase.upper.inv phase_upper_inv_exp h.2⟩⟩

/-- **The braided category of ordinary modules**, conditional only on the continuation
input (the braiding-free analytic content of Huang's hexagon theorem). -/
abbrev braidedCategory_of_continuation (hV : StronglyRational W)
    (h : HexagonContinuationInput F) :
    @BraidedCategory (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV) :=
  braidedCategoryOfStronglyRational_pbw F hV (hexagonInput_of_continuation F hV h)

end HexagonClose
end VOA.Huang.TensorCat
