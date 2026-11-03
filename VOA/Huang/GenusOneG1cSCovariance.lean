import VOA.Huang.GenusOneG1cDictionary

/-!
# S-covariance of the vacuum channel, conditional on the bracket-coordinate expansion

Step (b). Zhu's modularity (`ZhuModularityAnalytic D`, a standing hypothesis of
`VacuumChannelTransportInput`) transforms each one-point function `traceFun x v` with
`v ∈ V_[n]` (square-bracket weight `n`) by `τ^n Σ_y S_xy traceFun y v`. A *bracket channel*
`Σ_m coef_m · e^{(n_m − κ_m) ℓ} · traceFun x (v_m) τ` (`ℓ = log` of the torus coordinate) is
therefore S-covariant (`bracketChannel_S`, proved, no extra input):

  `bracketChannel coef x (ℓ − L) (S • τ) = Σ_y S_xy · bracketChannel (coef · e^{κ L}) y ℓ τ`,
  `e^L = τ`.

The genus-one input is the **coordinate change for intertwining operators** (Zhu's bracket
coordinates `Y[w, y] = Y(e^{y L(0)} w, e^y − 1)`, being formalized separately in
`VOA/Huang/GenusOneIntCoord*.lean`): the vacuum channel `Ψ_x = iterF Y_{M_x} (epsInt c)` is, up to a
factor depending on `z₀` only, a bracket channel with data independent of `x` and `τ`. It is
recorded as the named Prop `VacuumChannelBracketExpansion` (docstring: why it is true and what
each datum is), and (b) is proved conditional on it: `vacuumChannel_S_covariance`.

Conventions are not guessed: the Prop only asserts EXISTENCE of the prefactor `P(z₀)`
(`= (1+z₀)^{−α_a}` up to constants in Zhu's normalisation), the coefficients, the bracket
components `v_m ∈ V_[n_m]` and exponents `κ_m`; the S-law is invariant under the choice of
`2πi`-normalisation of the torus coordinate (it rescales `v_m` and `P`).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1c

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion
  Complex
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators MatrixGroups

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- A bracket channel: `Σ_m coef_m e^{(n_m − κ_m) ℓ} traceFun x (v_m) τ`. -/
def bracketChannel (D : VOA.ModularData W ι) (coef : ℕ → ℂ) (v : ℕ → 𝒱) (n : ℕ → ℕ)
    (κ : ℕ → ℂ) (x : ι) (ℓ : ℂ) (τ : UpperHalfPlane) : ℂ :=
  ∑' m, coef m * exp (((n m : ℂ) - κ m) * ℓ) * traceFun D.Mfam D.h x (v m) τ

theorem autFactor_S (τ : UpperHalfPlane) : autFactor ModularGroup.S τ = τ := by
  simp [autFactor, ModularGroup.S]

/-- **S-covariance of bracket channels** (Zhu's theorem, termwise). -/
theorem bracketChannel_S (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D)
    (coef : ℕ → ℂ) (v : ℕ → 𝒱) (n : ℕ → ℕ) (κ : ℕ → ℂ)
    (hv : ∀ m, v m ∈ sqWeightSpace W (n m : ℂ)) (x : ι) (ℓ L : ℂ) (τ : UpperHalfPlane)
    (hL : exp L = τ)
    (hsum : ∀ y, Summable fun m => coef m * exp (κ m * L) * exp (((n m : ℂ) - κ m) * ℓ) *
      traceFun D.Mfam D.h y (v m) τ) :
    bracketChannel D coef v n κ x (ℓ - L) (ModularGroup.S • τ) =
      ∑ y, D.repS x y * bracketChannel D (fun m => coef m * exp (κ m * L)) v n κ y ℓ τ := by
  have hterm : ∀ m, coef m * exp (((n m : ℂ) - κ m) * (ℓ - L)) *
      traceFun D.Mfam D.h x (v m) (ModularGroup.S • τ) =
      ∑ y, D.repS x y * (coef m * exp (κ m * L) * exp (((n m : ℂ) - κ m) * ℓ) *
        traceFun D.Mfam D.h y (v m) τ) := by
    intro m
    rw [hZ ModularGroup.S (n m) (v m) (hv m) x τ, autFactor_S, D.rep_S]
    simp only [Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hτ : (τ : ℂ) ^ (n m) = exp ((n m : ℂ) * L) := by
      rw [← hL, ← Complex.exp_nat_mul]
    rw [hτ]
    have : exp (((n m : ℂ) - κ m) * (ℓ - L)) * exp ((n m : ℂ) * L) =
        exp (κ m * L) * exp (((n m : ℂ) - κ m) * ℓ) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
    linear_combination (coef m * D.repS x y * traceFun D.Mfam D.h y (v m) τ) * this
  unfold bracketChannel
  rw [tsum_congr hterm, Summable.tsum_finsetSum (fun y _ => (hsum y).mul_left _)]
  exact Finset.sum_congr rfl fun y _ => by rw [tsum_mul_left]

variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-- **The coordinate change for the vacuum channel (named input for step (b)).**

For every pair of homogeneous insertions `w_a ∈ M_a(α_a)`, `w_b ∈ M_b(α_b)` there are a prefactor
`P(z₀)`, coefficients `coef_m`, square-bracket-homogeneous vectors `v_m ∈ V_[n_m]`, exponents `κ_m`
— ALL independent of the traced label `x` and of `τ` — and, for every `τ`, a radius `δ(τ) > 0`
(the bracket expansion converges only up to the nearest lattice point, so `δ` must depend on `τ`)
such that on the half-disc `{Re z₀ > 0, ‖z₀‖ < δ}` the vacuum-channel function of the dictionary
(`Ψ_x(z₀) = Tr_{M_x} Y_{M_x}(Y^e(w_a, z₀) w_b, 1) q^{L₀−c/24}`, `iterF … (epsInt c)`) equals
`P(z₀) · Σ_m coef_m · y^{n_m − κ_m} · traceFun x (v_m) τ`, `y = log(1 + z₀)` (principal powers,
`y^{e} = e^{e log y}`), the series converging absolutely for every `x`.

*Why it is true.* Bracket coordinates for intertwiners: `Y^e(w_a, e^y − 1) = Y^e[e^{−yL(0)} w_a, y]
= e^{−yα_a} Y^e[w_a, y]`, and `Y^e[w_a, y] w_b = Σ_k (w_a)[k] w_b y^{−k−1}`; splitting `w_a, w_b`
into `L[0]`-eigencomponents of weights `ω, ω'` (finitely many), `(w_a)[k] w_b ∈ V_[n]` with
`−k−1 = n − κ`, `κ = ω + ω'`. Tracing `Y_{M_x}(v, 1) q^{L₀}` gives `Tr o(v) q^{L₀}`, i.e. the
one-point function `traceFun x v` (`torusOnePoint`). So `P(z₀) = (1+z₀)^{−α_a}`, `v_m` the bracket
components, `κ_m = ω + ω'`. The convergence (interchange of the bracket expansion with the
genus-one trace) is the analytic content of the change of coordinates (Zhu 1996 §5, Huang 2005
for intertwiners), being formalized in `VOA/Huang/GenusOneIntCoord*.lean`. -/
def VacuumChannelBracketExpansion (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b) : Prop :=
  ∀ {αa αb : ℂ} {wa : (lwOf D a).carrier} {wb : (lwOf D b).carrier},
    wa ∈ (lwOf D a).isMod.weight αa → wb ∈ (lwOf D b).isMod.weight αb →
    ∃ (P : ℂ → ℂ) (coef : ℕ → ℂ) (v : ℕ → 𝒱) (n : ℕ → ℕ) (κ : ℕ → ℂ),
      (∀ m, v m ∈ sqWeightSpace W (n m : ℂ)) ∧
      ∀ τ : UpperHalfPlane, ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι) (z₀ : ℂ), 0 < z₀.re → ‖z₀‖ < δ →
        Summable (fun m => coef m * exp (((n m : ℂ) - κ m) * log (log (1 + z₀))) *
          traceFun D.Mfam D.h x (v m) τ) ∧
        iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
            (epsInt F c) wa wb αa αb τ z₀ =
          P z₀ * bracketChannel D coef v n κ x (log (log (1 + z₀))) τ

/-- **(b) S-covariance of the vacuum channel, conditional on the coordinate change.**
Given `VacuumChannelBracketExpansion` and Zhu's modularity of `D`, the vacuum channels are
`P(z₀)` times bracket channels whose S-transforms are `Σ_y S_xy ·` (bracket channels of the
same data with coefficients rescaled by `e^{κ_m L}`, `e^L = τ`), at every point where the
rescaled series converge. -/
theorem vacuumChannel_S_covariance (hZ : ZhuModularityAnalytic D) (hv : W.vacuum ≠ 0)
    (c : TransferChoice F D a b) (hexp : VacuumChannelBracketExpansion F hv c)
    {αa αb : ℂ} {wa : (lwOf D a).carrier} {wb : (lwOf D b).carrier}
    (hwa : wa ∈ (lwOf D a).isMod.weight αa) (hwb : wb ∈ (lwOf D b).isMod.weight αb) :
    ∃ (P : ℂ → ℂ) (coef : ℕ → ℂ) (v : ℕ → 𝒱) (n : ℕ → ℕ) (κ : ℕ → ℂ),
      (∀ τ : UpperHalfPlane, ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ι) (z₀ : ℂ), 0 < z₀.re → ‖z₀‖ < δ →
        iterF (Q := vacuumLW W hv) (N := lwOf D x) (moduleIntertwiner (lwOf D x).isMod)
            (epsInt F c) wa wb αa αb τ z₀ =
          P z₀ * bracketChannel D coef v n κ x (log (log (1 + z₀))) τ) ∧
      ∀ (x : ι) (ℓ L : ℂ) (τ : UpperHalfPlane), exp L = τ →
        (∀ y, Summable fun m => coef m * exp (κ m * L) * exp (((n m : ℂ) - κ m) * ℓ) *
          traceFun D.Mfam D.h y (v m) τ) →
        bracketChannel D coef v n κ x (ℓ - L) (ModularGroup.S • τ) =
          ∑ y, D.repS x y * bracketChannel D (fun m => coef m * exp (κ m * L)) v n κ y ℓ τ := by
  obtain ⟨P, coef, v, n, κ, hvn, hE⟩ := hexp hwa hwb
  refine ⟨P, coef, v, n, κ, fun τ => ?_,
    fun x ℓ L τ hL hsum => bracketChannel_S D hZ coef v n κ hvn x ℓ L τ hL hsum⟩
  obtain ⟨δ, hδ, h⟩ := hE τ
  exact ⟨δ, hδ, fun x z₀ hre hn => (h x z₀ hre hn).2⟩

end VOA.Huang.GenusOneG1c
