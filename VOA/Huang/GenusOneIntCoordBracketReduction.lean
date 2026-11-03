import VOA.Huang.GenusOneIntCoordLogExpansion

/-!
# The exact G1c bracket expansion from a concrete summability estimate

The prefactor is `z^(-α-β)`. The scalar Taylor degree is `r`, the square weight
is `n`, and `κ = n-r`, so the exponent required by G1c is exactly `r`.
This uses the full freedom of the existing definition: κ need not be a sum of
input weights. The analytic estimate `LogSquareTraceSummable` is not proved here.
-/

noncomputable section
namespace VOA.Huang.GenusOne.IntCoord
open VOA GenusTwoPoint GenusOneG1c VerlindeFusion VerlindeTransport TensorCat Complex
open scoped BigOperators

/-- Fixed enumeration of inner degree, square weight, and scalar Taylor degree. -/
def bracketIndex : ℕ ≃ ℕ × (ℕ × ℕ) :=
  Nat.pairEquiv.symm.trans (Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv.symm)

theorem log_coordinate_nonzero {z : ℂ} (hz : 0 < z.re) :
    z ≠ 0 ∧ 1 + z ≠ 0 ∧ log (1 + z) ≠ 0 := by
  have h0 : z ≠ 0 := fun he => by simp [he] at hz
  have h1 : 1 + z ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  refine ⟨h0, h1, fun he => ?_⟩
  have h := congrArg exp he
  rw [Complex.exp_log h1, Complex.exp_zero] at h
  exact h0 (by linear_combination h)

theorem bracket_log_power (n r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    exp (((n : ℂ) - ((n : ℂ) - r)) * log (log (1 + z))) = log (1 + z) ^ r := by
  rw [show (n : ℂ) - ((n : ℂ) - r) = (r : ℂ) by ring,
    Complex.exp_nat_mul, Complex.exp_log (log_coordinate_nonzero hz).2.2]

universe u w
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {ι : Type w} [Fintype ι] [DecidableEq ι] {D : VOA.ModularData W ι}

/-- The exact requested Prop, conditional only on the explicit analytic joint
estimate for the canonical square components of the vacuum inner coefficients.
Neither a formal nor an analytic intertwiner substitution is a hypothesis. -/
theorem vacuumChannelBracketExpansion_of_logSquareTraceSummable
    (hV : StronglyRational W) (F : FusionChoice W) (hv : W.vacuum ≠ 0)
    {a b : ι} (c : TransferChoice F D a b)
    (hlog : ∀ {α β : ℂ} {wa : (lwOf D a).carrier} {wb : (lwOf D b).carrier},
      wa ∈ (lwOf D a).isMod.weight α → wb ∈ (lwOf D b).isMod.weight β →
        LogSquareTraceSummable D (epsInt F c) wa wb α β) :
    VacuumChannelBracketExpansion F hv c := by
  intro α β wa wb hwa hwb
  let coef : ℕ → ℂ := fun m => expSubOneCoeff (bracketIndex m).1 (bracketIndex m).2.2
  let v : ℕ → V := fun m => squarePart (W := W)
    (vacuumInnerCoeff (epsInt F c) wa wb α β (bracketIndex m).1) (bracketIndex m).2.1
  let n : ℕ → ℕ := fun m => (bracketIndex m).2.1
  let κ : ℕ → ℂ := fun m => (n m : ℂ) - (bracketIndex m).2.2
  refine ⟨fun z => z ^ (-α - β), coef, v, n, κ,
    fun m => squarePart_mem _ _, fun τ => ?_⟩
  obtain ⟨δp, hδp, hplane⟩ := vacuumChannel_plane_expansion D hV F hv c hwa hwb τ
  obtain ⟨δl, hδl, hlogs⟩ := hlog hwa hwb τ
  refine ⟨min δp δl, lt_min hδp hδl, fun x z hz hnorm => ?_⟩
  have hs := hlogs x z hz (hnorm.trans_le (min_le_right _ _))
  have hp := hplane x z hz (hnorm.trans_le (min_le_left _ _))
  have ht : ∀ m : ℕ,
      coef m * exp (((n m : ℂ) - κ m) * log (log (1 + z))) *
        traceFun D.Mfam D.h x (v m) τ =
      logSquareTerm D (epsInt F c) wa wb α β x τ z (bracketIndex m) := by
    intro m
    dsimp only [coef, n, κ, v, logSquareTerm]
    rw [bracket_log_power _ _ hz]
  constructor
  · exact (bracketIndex.summable_iff.mpr hs).congr fun m => (ht m).symm
  · change _ = z ^ (-α - β) * ∑' m : ℕ,
      coef m * exp (((n m : ℂ) - κ m) * log (log (1 + z))) *
        traceFun D.Mfam D.h x (v m) τ
    rw [tsum_congr ht, bracketIndex.tsum_eq,
      logSquareTerm_tsum D hV.c2Cofinite (epsInt F c) wa wb α β x τ
        (log_coordinate_nonzero hz).2.1 hs, ← tsum_mul_left]
    exact hp.tsum_eq.symm.trans (tsum_congr fun k => by
      rw [planePower_eq α β z (log_coordinate_nonzero hz).1]; ring)

end VOA.Huang.GenusOne.IntCoord
