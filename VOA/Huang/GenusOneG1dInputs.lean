import VOA.Huang.GenusOneG1dCell
import VOA.Huang.GenusOneG1cBCycleComplex
import VOA.Huang.GenusOneG1cACycleOne
import VOA.Huang.GenusOneSquareModes

/-!
# The genus-one function layer of (G1), and the four named genus-one inputs

Step (4b) of the proof of (G1).

**Insertions.** `Insertion D a b` is a pair of vectors `w_a = Σ_i w_{a,i}`, `w_b = Σ_j w_{b,j}`
given by their `L(0)`-homogeneous components (weights `α_{a,i}`, `α_{b,j}`, the latter on the
lowest-weight coset `h_b + ℕ`), such that the sums are `L[0]`-homogeneous (square weights
`ω_a`, `ω_b`; `κ = ω_a + ω_b`). `L[0]`-homogeneity is what makes the vacuum channel a single
`τ^κ`-covariant function (Zhu); `L(0)`-homogeneity of the components is what the convergence and
the A/B-cycle theorems use. Every vector is a finite sum of `L[0]`-homogeneous ones.

**Functions** (torus coordinate `u = log(1 + z₀)`, `z₀ = e^u − 1` the collision variable):
* `vacF c ins x τ u = Σ_{i,j} e^{α_{a,i} u} Ψ_x(z₀)` — Huang's vacuum channel of `(a,b)`, traced
  over `M_x`, normalised to the torus frame (Zhu's bracket field `Y[w_a, u]`);
* `revF π ins z τ u = Σ_{i,j} e^{α_{b,j} u} Φ_z(z₀)` — the vacuum channel of the reversed pair
  `(b,a)` with pairing `π` (the right side of the B-cycle theorem);
* `prodN c x ins τ u = Σ_{i,j,k} cellF μ_k ν_k` — the product channel on the strip;
* `ABChannel η'` / `BAChannel η` — iterate channels whose inner morphism `q` is orthogonal to the
  vacuum summand (`η' ≫ q = 0`, resp. `η ≫ q = 0`); `ABChannel.eval`, `BAChannel.eval`.

**The non-vacuum span** `Rspan` (item 2 of the G1 task): the `ℂ`-span, in the space of functions of
`(insertion, τ, u)`, of all `(a,b)`-orthogonal channels and of `e^{iπκ}` times all
`(b,a)`-orthogonal channels, plus the functions vanishing on a small `sector` at every
`(insertion, τ)` (equality of germs). Coefficients of a span element are constants, uniform in
the insertion and in `τ` (Huang's Prop. 2.11 is about such combinations).

**The four named inputs** (all TRUE by Zhu 1996 / Huang 2005, 2008; none is equivalent to (G1);
see each docstring):
* `VacuumSCovariance` — near-collision S-covariance of the vacuum channel (Huang's step (i), the
  "clearly" before Thm 4.6; from the bracket-coordinate expansion and Zhu's theorem);
* `ConjugationInput` — the reversed-pair vacuum channel is `λ₀ e^{−iπκ}` times the vacuum channel
  traced over the conjugate module (genus-zero skew-symmetry + `Z(L[−1]v) = 0` + Zhu's
  `ρ(−1) = C`);
* `ChannelSStability` — the `S`-transform of an `(a,b)`-orthogonal channel lies in `Rspan`
  (Huang/Miyamoto modular invariance of intertwiner one-point functions, `InsertionSClosure`);
* `ChannelIndependence` — Huang's Prop. 2.11: the vacuum channels are linearly independent modulo
  `Rspan`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1d

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.GenusOneG1c CategoryTheory
  Complex
open VOA.Huang.GenusTwoPoint (vacuumLW)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## §1 Insertions -/

/-- An insertion: `L(0)`-components of `w_a`, `w_b` whose sums are `L[0]`-homogeneous. -/
structure Insertion (D : VOA.ModularData W ι) (a b : ι) where
  /-- number of components of `w_a` -/
  m : ℕ
  /-- number of components of `w_b` -/
  n : ℕ
  /-- the components of `w_a` -/
  wa : Fin m → (lwOf D a).carrier
  /-- their `L(0)`-weights -/
  αa : Fin m → ℂ
  hwa : ∀ i, wa i ∈ (lwOf D a).isMod.weight (αa i)
  /-- the components of `w_b` -/
  wb : Fin n → (lwOf D b).carrier
  /-- their `L(0)`-weights -/
  αb : Fin n → ℂ
  hwb : ∀ j, wb j ∈ (lwOf D b).isMod.weight (αb j)
  /-- the `w_b`-weights lie on the lowest-weight coset -/
  hlev : ∀ j, ∃ k : ℕ, αb j = D.h b + k
  /-- square weight of `w_a` -/
  ωa : ℂ
  /-- square weight of `w_b` -/
  ωb : ℂ
  hsqa : GenusOne.sqL (lwOf D a).isMod 0 (∑ i, wa i) = ωa • ∑ i, wa i
  hsqb : GenusOne.sqL (lwOf D b).isMod 0 (∑ j, wb j) = ωb • ∑ j, wb j

/-- `κ = ω_a + ω_b`. -/
def Insertion.κ {D : VOA.ModularData W ι} {a b : ι} (ins : Insertion D a b) : ℂ :=
  ins.ωa + ins.ωb

/-! ## §2 The functions -/

variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-- The vacuum channel of `(a, b)` traced over `M_x`, in the torus frame. -/
def vacF (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b) (ins : Insertion D a b) (x : ι)
    (τ : UpperHalfPlane) (u : ℂ) : ℂ :=
  ∑ i, ∑ j, exp (ins.αa i * u) * iterF (Q := vacuumLW W hv) (N := lwOf D x)
    (moduleIntertwiner (lwOf D x).isMod) (epsInt F c) (ins.wa i) (ins.wb j) (ins.αa i)
    (ins.αb j) τ (exp u - 1)

/-- The vacuum channel of the reversed pair `(b, a)` (pairing `π`) traced over `M_z`. -/
def revF (hv : W.vacuum ≠ 0) (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject)
    (ins : Insertion D a b) (z : ι) (τ : UpperHalfPlane) (u : ℂ) : ℂ :=
  ∑ i, ∑ j, exp (ins.αb j * u) * iterF (Q := vacuumLW W hv) (N := lwOf D z)
    (moduleIntertwiner (lwOf D z).isMod) (piInt F π) (ins.wb j) (ins.wa i) (ins.αb j)
    (ins.αa i) τ (exp u - 1)

/-- The product expansion of the vacuum channel, on the strip. -/
def prodN (c : TransferChoice F D a b) (x : ι) (ins : Insertion D a b) (τ : UpperHalfPlane)
    (u : ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, cellF (Q := lwOf D (c.lab x k)) (N := lwOf D x) (muInt F H c x k)
    (nuInt F c x k) (ins.wa i) (ins.wb j) (ins.αa i) (ins.αb j) τ u

/-- An `(a,b)` iterate channel through `M_k`, traced over `M_y`, whose inner morphism is
orthogonal to the vacuum summand `η'` of `M_a ⊠ M_b`. -/
structure ABChannel (F : FusionChoice W) (D : VOA.ModularData W ι) (a b : ι)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) where
  /-- inner label -/
  k : ι
  /-- traced label -/
  y : ι
  /-- inner morphism -/
  q : tensorObj F (famObj D a) (famObj D b) ⟶ famObj D k
  hq : η' ≫ q = 0
  /-- outer intertwiner -/
  Yout : IntertwiningOperator (lwOf D k).isMod (lwOf D y).isMod (lwOf D y).isMod

/-- A `(b,a)` iterate channel, orthogonal to the vacuum summand `η` of `M_b ⊠ M_a`. -/
structure BAChannel (F : FusionChoice W) (D : VOA.ModularData W ι) (a b : ι)
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) where
  /-- inner label -/
  k : ι
  /-- traced label -/
  y : ι
  /-- inner morphism -/
  q : tensorObj F (famObj D b) (famObj D a) ⟶ famObj D k
  hq : η ≫ q = 0
  /-- outer intertwiner -/
  Yout : IntertwiningOperator (lwOf D k).isMod (lwOf D y).isMod (lwOf D y).isMod

variable {F}

/-- The inner intertwiner of an `(a,b)` channel. -/
def ABChannel.inner {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (C : ABChannel F D a b η') :
    IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod (lwOf D C.k).isMod :=
  postcompose (F (famObj D a) (famObj D b)).intertwiner (lwOf D C.k).isMod C.q

/-- The inner intertwiner of a `(b,a)` channel. -/
def BAChannel.inner {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (C : BAChannel F D a b η) :
    IntertwiningOperator (lwOf D b).isMod (lwOf D a).isMod (lwOf D C.k).isMod :=
  postcompose (F (famObj D b) (famObj D a)).intertwiner (lwOf D C.k).isMod C.q

/-- An `(a,b)` channel as a function, in the torus frame. -/
def ABChannel.eval {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    (C : ABChannel F D a b η') (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) : ℂ :=
  ∑ i, ∑ j, exp (ins.αa i * u) * iterF (Q := lwOf D C.k) (N := lwOf D C.y) C.Yout C.inner
    (ins.wa i) (ins.wb j) (ins.αa i) (ins.αb j) τ (exp u - 1)

/-- A `(b,a)` channel as a function, in the torus frame of the reversed pair. -/
def BAChannel.eval {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (C : BAChannel F D a b η) (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) : ℂ :=
  ∑ i, ∑ j, exp (ins.αb j * u) * iterF (Q := lwOf D C.k) (N := lwOf D C.y) C.Yout C.inner
    (ins.wb j) (ins.wa i) (ins.αb j) (ins.αa i) τ (exp u - 1)

/-! ## §3 The non-vacuum span -/

/-- The small sector near the collision used by the B-cycle/A-cycle bookkeeping:
`‖u‖ < δ`, `Re(e^u − 1) > 0`, `Re(e^{−u/τ} − 1) > 0`. -/
def sector (τ : UpperHalfPlane) (δ : ℝ) : Set ℂ :=
  {u | ‖u‖ < δ ∧ 0 < (exp u - 1).re ∧ 0 < (exp (-u / τ) - 1).re}

/-- The space of functions of `(insertion, τ, u)`. -/
abbrev FunSpace (D : VOA.ModularData W ι) (a b : ι) : Type u :=
  Insertion D a b → UpperHalfPlane → ℂ → ℂ

/-- Functions vanishing on a small sector at every `(insertion, τ)` (zero germs). -/
def germZero (D : VOA.ModularData W ι) (a b : ι) : Submodule ℂ (FunSpace D a b) where
  carrier := {g | ∀ ins τ, ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ sector τ δ, g ins τ u = 0}
  zero_mem' := fun _ _ => ⟨1, one_pos, fun _ _ => rfl⟩
  add_mem' := by
    intro g g' hg hg' ins τ
    obtain ⟨δ, hδ, h⟩ := hg ins τ
    obtain ⟨δ', hδ', h'⟩ := hg' ins τ
    refine ⟨min δ δ', lt_min hδ hδ', fun u hu => ?_⟩
    have hu1 : u ∈ sector τ δ := ⟨lt_of_lt_of_le hu.1 (min_le_left _ _), hu.2⟩
    have hu2 : u ∈ sector τ δ' := ⟨lt_of_lt_of_le hu.1 (min_le_right _ _), hu.2⟩
    change g ins τ u + g' ins τ u = 0
    rw [h u hu1, h' u hu2, add_zero]
  smul_mem' := by
    intro t g hg ins τ
    obtain ⟨δ, hδ, h⟩ := hg ins τ
    exact ⟨δ, hδ, fun u hu => by change t * g ins τ u = 0; rw [h u hu, mul_zero]⟩

/-- The generators of the non-vacuum span: all `(a,b)`-orthogonal channels and `e^{iπκ}` times
all `(b,a)`-orthogonal channels. -/
def nonVacGen (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) :
    Set (FunSpace D a b) :=
  Set.range (fun C : ABChannel F D a b η' => fun ins τ u => C.eval ins τ u) ∪
    Set.range (fun C : BAChannel F D a b η => fun ins τ u =>
      exp ((Real.pi : ℂ) * I * ins.κ) * C.eval ins τ u)

/-- **The non-vacuum span `R`** (item 2): span of the orthogonal channels, modulo zero germs. -/
def Rspan (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) :
    Submodule ℂ (FunSpace D a b) :=
  Submodule.span ℂ (nonVacGen η' η) ⊔ germZero D a b

/-! ## §4 The four named inputs -/

variable (F)

/-- **(N1) Near-collision S-covariance of the vacuum channel** (Huang 2008, step (i) before
Thm 4.6). For every insertion and every `τ`, for small `u` with `Re(e^u − 1) > 0` and
`Re(e^{u/τ} − 1) > 0` (both points on the convergent side of the collision):
`vacF x (S τ) (u/τ) = τ^κ Σ_y S_xy vacF y τ u`, `τ^κ = e^{κ log τ}` (principal).

*Why it is true.* With `w_a, w_b` `L[0]`-homogeneous, `vacF x τ u = Tr_{M_x} Y(Y^e[w_a, u] w_b, 1)
q^{L₀−c/24} = Σ_m u^{m−κ} Z_x(v_m, τ)` with `v_m ∈ V_[m]` the bracket components (Zhu's coordinate
change for the intertwiner `Y^e`, normalised by `e^{α_{a,i} u}` per component). Zhu's theorem
`Z_x(v_m, S τ) = τ^m Σ_y S_xy Z_y(v_m, τ)` and `(u/τ)^{m−κ} = u^{m−κ} τ^{κ−m}` (both `u` and `u/τ`
in the right half-plane, so `log(u/τ) = log u − log τ`) give the identity termwise. This is the
content of `GenusOneG1c.VacuumChannelBracketExpansion` in the sharp form (explicit prefactor,
constant `κ`); from the data of the existing existential Prop alone it cannot be derived by the
bracket route (see `### G1 outcome (part 4)`, dead end 1). -/
def VacuumSCovariance (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b) : Prop :=
  ∀ (ins : Insertion D a b) (τ : UpperHalfPlane), ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ →
    0 < (exp u - 1).re → 0 < (exp (u / τ) - 1).re → ∀ x,
      vacF F hv c ins x (ModularGroup.S • τ) (u / τ) =
        exp (ins.κ * log τ) * ∑ y, D.repS x y * vacF F hv c ins y τ u

/-- **(N2) The conjugation identity for the reversed pair.** For a vacuum retraction `π` of the
vacuum summand of `M_b ⊠ M_a` and the charge conjugation `σ` (`ρ(−1) = P_σ`), there is `λ₀ ≠ 0`
with `revF π z = λ₀ e^{−iπκ} vacF (σ z)` near the collision, for every insertion and `τ`.

*Why it is true.* Genus-zero skew-symmetry (`π ∘ braiding ∝ ε`, `Hom(M_a ⊠ M_b, V)` one-dimensional)
gives `Y^π[w_b, u] w_a = μ e^{u L[−1]} Y^e[w_a, e^{iπ} u] w_b`; Zhu's `Z_x(L[−1] v) = 0` kills
`e^{u L[−1]}`; `(e^{iπ}u)^{m−κ} = e^{−iπκ}(−1)^m u^{m−κ}`; Zhu's theorem at `−1 ∈ SL₂(ℤ)` with
`ρ(−1) = P_σ` gives `(−1)^m Z_x(v) = Z_{σx}(v)` for `v ∈ V_[m]`. Hence `revF π x = μ e^{−iπκ}
vacF (σ x)`. (The other skew phase `e^{−iπ}` changes `μ` by `e^{2πiκ}`, constant on nonzero
insertions since `κ ∈ h_a + h_b + ℤ`.) -/
def ConjugationInput (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (π : tensorObj F (famObj D b) (famObj D a) ⟶ vacuumObject) (σ : ι → ι) : Prop :=
  ∃ μ : ℂ, μ ≠ 0 ∧ ∀ (ins : Insertion D a b) (τ : UpperHalfPlane), ∃ δ : ℝ, 0 < δ ∧
    ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re → ∀ z,
      revF F hv π ins z τ u = μ * exp (-((Real.pi : ℂ) * I * ins.κ)) * vacF F hv c ins (σ z) τ u

/-- **(N3) S-stability of the non-vacuum span** (item 2). The `S`-transform of an
`(a,b)`-orthogonal channel, `e^{iπκ} τ^{−κ} C(S τ, −u/τ)`, lies in `Rspan`.

*Why it is true.* The bracket expansion of `C` has coefficients the one-point functions
`Tr_{M_y} o_{Y_out}(u_m) q^{L₀−c/24}` of the intertwiners of type `(M_y / M_k M_y)` at the bracket
components `u_m ∈ M_k` of `Y_in[w_a, u] w_b`; their `S`-transforms are combinations of such
functions with the SAME inner part, coefficients uniform in the insertion and `τ`
(`GenusOne.Close.insertionSClosure_of_stronglyRational_pbw`, proved). With `S² = ±C` the
`S`-action on this finite-dimensional family is invertible; the factor
`e^{iπκ} τ^{−κ} (S τ)^{−κ} = 1` (`log τ + log(S τ) = iπ`). -/
def ChannelSStability
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)) : Prop :=
  ∀ C : ABChannel F D a b η',
    (fun (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) =>
      exp ((Real.pi : ℂ) * I * ins.κ) * exp (-(ins.κ * log τ)) *
        C.eval ins (ModularGroup.S • τ) (-u / τ)) ∈ Rspan η' η

/-- **(N4) Huang's Prop. 2.11: independence of the vacuum channels modulo the non-vacuum span.**

*Why it is true.* A span element is a combination, with constant coefficients, of iterate channels
whose inner channel avoids the vacuum summand (the `(b,a)` ones become such `(a,b)` channels traced
over conjugate modules by the mechanism of (N2), which is why they carry `e^{iπκ}`). Expanding in
`z₀` and `q`, the coefficient functionals of `(w_a, w_b)` factor through `M_a ⊠ M_b`; the vacuum
ones through `ε`, the others vanish on the vacuum summand. Precomposing with a section of `ε` and
using the linear independence of the Zhu trace functions of distinct irreducibles gives `c = 0`
(Huang 2008, Prop. 2.11). NOT via local exponents (they coincide mod `ℤ` at `c = 1`). The sector is
nonempty (`sector_nonempty`), so the hypothesis is not vacuous. -/
def ChannelIndependence (hv : W.vacuum ≠ 0) (c : TransferChoice F D a b)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)) : Prop :=
  ∀ coef : ι → ℂ,
    (fun (ins : Insertion D a b) (τ : UpperHalfPlane) (u : ℂ) =>
      ∑ z, coef z * vacF F hv c ins z τ u) ∈ Rspan η' c.η → coef = 0

/-! ## §5 Non-vacuity of the sector -/

/-- The sector is nonempty at every `τ` and every radius: the independence input is not vacuous. -/
theorem sector_nonempty (τ : UpperHalfPlane) {δ : ℝ} (hδ : 0 < δ) : (sector τ δ).Nonempty := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hn : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr hτ
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have hre : |(τ : ℂ).re| < ‖(τ : ℂ)‖ := by
    have h := Complex.abs_re_lt_norm.mpr (by
      intro h0; rw [h0] at him; exact lt_irrefl _ him)
    exact h
  set v : ℂ := (‖(τ : ℂ)‖ : ℂ) - τ with hv
  have hv1 : 0 < v.re := by
    rw [hv, Complex.sub_re, Complex.ofReal_re]
    linarith [le_abs_self (τ : ℂ).re]
  have hv2 : 0 < (v * (-1 / τ)).re := by
    have : v * (-1 / τ) = 1 - (‖(τ : ℂ)‖ : ℂ) / τ := by
      rw [hv]; field_simp; ring
    rw [this, Complex.sub_re, Complex.one_re, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, zero_div, add_zero, Complex.normSq_eq_norm_sq]
    have h1 : ‖(τ : ℂ)‖ * (τ : ℂ).re / ‖(τ : ℂ)‖ ^ 2 = (τ : ℂ).re / ‖(τ : ℂ)‖ := by
      field_simp
    rw [h1, sub_pos, div_lt_one hn]
    linarith [le_abs_self (τ : ℂ).re]
  obtain ⟨r, hr0, hrn, h1, h2⟩ := exists_small_re_exp hv1 hv2 hδ
  refine ⟨(r : ℂ) * v, hrn, h1, ?_⟩
  have : -((r : ℂ) * v) / τ = (r : ℂ) * v * (-1 / τ) := by ring
  rw [this]
  exact h2

end VOA.Huang.GenusOneG1d
