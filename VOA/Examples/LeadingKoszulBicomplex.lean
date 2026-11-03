/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Abel

/-!
# The Koszul–Chevalley–Eilenberg bicomplex at ghost number zero

This file proves, by an explicit zigzag, the collapse step of the explicit leading contraction in
the coset BRST–Koszul transfer argument (with the shifted grading).

## The datum

The leading differential is `Q⁻ = d_K + d_CE` on a bicomplex `T^{p,q}`, where `p` is the
number of antighost (Koszul) generators `b` and `q` the number of ghosts `c`; the ghost
number is `q - p`. `d_K : T^{p,q} → T^{p-1,q}` preserves the `c`-count and `d_CE` raises it
by one. Only four diagonals of the bicomplex enter the ghost-number-zero cohomology:

* `Y p = T^{p+1,p}` (ghost number `-1`), `X p = T^{p,p}` (ghost number `0`),
* `Z p = T^{p,p+1}` (ghost number `+1`), `G p = T^{p,p+2}` (ghost number `+2`).

The six components of `d_K` and `d_CE` between them are the fields of `LeadingBicomplex`.
The hypotheses are exactly:

* the components of `(d_K + d_CE)² = 0` that are used (`rel_YZ`, `rel_YY`, `rel_KK`,
  `rel_XG`, `rel_CC`);
* **Koszul exactness in positive antighost degree** at the two positions met by the zigzag
  (`exact_X` at `T^{p+1,p+1}`, `exact_Z` at `T^{p+1,p+2}`).

No finiteness is assumed: the total complex is the *product* totalization `∀ p, X p`. At a
fixed conformal weight the bicomplex is finite, so this agrees with the direct-sum
totalization there.

## The result

`LeadingBicomplex.equivKer` : the ghost-number-zero total cohomology `H⁰(d_K + d_CE)` is
linearly isomorphic to the kernel of the map
`d̄_CE : H₀^K(row 0) = X 0 / d_K(Y 0) → H₀^K(row 1) = Z 0 / d_K(X 1)` induced by `d_CE`.
This is the collapse of the `c`-count spectral sequence onto the single Koszul row, proved
by hand (no spectral-sequence library). Everything is proved outright from the listed
hypotheses.
-/

namespace VOA.LeadingKoszul

universe u v

variable (R : Type u) [CommRing R]
variable (X Y Z G : ℕ → Type v)
variable [∀ p, AddCommGroup (X p)] [∀ p, Module R (X p)]
variable [∀ p, AddCommGroup (Y p)] [∀ p, Module R (Y p)]
variable [∀ p, AddCommGroup (Z p)] [∀ p, Module R (Z p)]
variable [∀ p, AddCommGroup (G p)] [∀ p, Module R (G p)]

/-- **The four ghost diagonals of the Koszul–Chevalley–Eilenberg bicomplex**, with the
components of `d_K` and `d_CE` between them. Indices: `Y p = T^{p+1,p}`, `X p = T^{p,p}`,
`Z p = T^{p,p+1}`, `G p = T^{p,p+2}` (first index: antighost count, second: ghost count). -/
structure LeadingBicomplex where
  /-- `d_K : T^{p+1,p} → T^{p,p}`. -/
  dKY : ∀ p, Y p →ₗ[R] X p
  /-- `d_CE : T^{p+1,p} → T^{p+1,p+1}`. -/
  dCEY : ∀ p, Y p →ₗ[R] X (p + 1)
  /-- `d_K : T^{p+1,p+1} → T^{p,p+1}`. -/
  dKX : ∀ p, X (p + 1) →ₗ[R] Z p
  /-- `d_CE : T^{p,p} → T^{p,p+1}`. -/
  dCEX : ∀ p, X p →ₗ[R] Z p
  /-- `d_K : T^{p+1,p+2} → T^{p,p+2}`. -/
  dKZ : ∀ p, Z (p + 1) →ₗ[R] G p
  /-- `d_CE : T^{p,p+1} → T^{p,p+2}`. -/
  dCEZ : ∀ p, Z p →ₗ[R] G p
  /-- `d_CE d_K + d_K d_CE = 0` on `T^{p+1,p}`. -/
  rel_YZ : ∀ p y, dCEX p (dKY p y) + dKX p (dCEY p y) = 0
  /-- `d_CE² = 0` on `T^{p+1,p}`. -/
  rel_YY : ∀ p y, dCEX (p + 1) (dCEY p y) = 0
  /-- `d_K² = 0` on `T^{p+2,p+1}`. -/
  rel_KK : ∀ p y, dKX p (dKY (p + 1) y) = 0
  /-- `d_K d_CE + d_CE d_K = 0` on `T^{p+1,p+1}`. -/
  rel_XG : ∀ p x, dKZ p (dCEX (p + 1) x) + dCEZ p (dKX p x) = 0
  /-- `d_CE² = 0` on `T^{p,p}`. -/
  rel_CC : ∀ p x, dCEZ p (dCEX p x) = 0
  /-- Koszul exactness at `T^{p+1,p+1}` (positive antighost degree). -/
  exact_X : ∀ p (x : X (p + 1)), dKX p x = 0 → ∃ y, dKY (p + 1) y = x
  /-- Koszul exactness at `T^{p+1,p+2}` (positive antighost degree). -/
  exact_Z : ∀ p (z : Z (p + 1)), dKZ p z = 0 → ∃ x, dKX (p + 1) x = z

namespace LeadingBicomplex

variable {R X Y Z G}
variable (B : LeadingBicomplex R X Y Z G)

/-! ### The total complex at ghost numbers `-1, 0, +1` -/

/-- Component `p` of the total differential on ghost number `-1`. -/
def DmComp : (p : ℕ) → (∀ q, Y q) →ₗ[R] X p
  | 0 => (B.dKY 0).comp (LinearMap.proj 0)
  | p + 1 => (B.dKY (p + 1)).comp (LinearMap.proj (p + 1)) + (B.dCEY p).comp (LinearMap.proj p)

/-- The total differential `d_K + d_CE` from ghost number `-1` to ghost number `0`. -/
def Dm : (∀ q, Y q) →ₗ[R] (∀ p, X p) := LinearMap.pi B.DmComp

/-- The total differential `d_K + d_CE` from ghost number `0` to ghost number `+1`. -/
def D0 : (∀ p, X p) →ₗ[R] (∀ p, Z p) :=
  LinearMap.pi fun p => (B.dCEX p).comp (LinearMap.proj p) + (B.dKX p).comp (LinearMap.proj (p + 1))

@[simp] theorem Dm_zero (y : ∀ q, Y q) : B.Dm y 0 = B.dKY 0 (y 0) := rfl

@[simp] theorem Dm_succ (y : ∀ q, Y q) (p : ℕ) :
    B.Dm y (p + 1) = B.dKY (p + 1) (y (p + 1)) + B.dCEY p (y p) := rfl

@[simp] theorem D0_apply (x : ∀ p, X p) (p : ℕ) :
    B.D0 x p = B.dCEX p (x p) + B.dKX p (x (p + 1)) := rfl

theorem D0_Dm (y : ∀ q, Y q) : B.D0 (B.Dm y) = 0 := by
  funext p
  rcases p with _ | p
  · simp only [D0_apply, Dm_zero, Dm_succ, map_add, Pi.zero_apply, B.rel_KK, zero_add]
    exact B.rel_YZ 0 (y 0)
  · simp only [D0_apply, Dm_succ, map_add, Pi.zero_apply, B.rel_KK, B.rel_YY, add_zero,
      zero_add]
    exact B.rel_YZ (p + 1) (y (p + 1))

/-- Ghost-number-zero total cycles. -/
def cycles : Submodule R (∀ p, X p) := LinearMap.ker B.D0

/-- Ghost-number-zero total boundaries, inside the cycles. -/
def boundaries : Submodule R B.cycles := (LinearMap.range B.Dm).comap B.cycles.subtype

/-- **The ghost-number-zero total cohomology** `H⁰(d_K + d_CE)`. -/
abbrev H0 := B.cycles ⧸ B.boundaries

/-! ### The Koszul row and the induced Chevalley–Eilenberg map -/

/-- Koszul `H₀` in `c`-count zero: `X 0 / d_K(Y 0)`. -/
abbrev KH0 := X 0 ⧸ LinearMap.range (B.dKY 0)

/-- Koszul `H₀` in `c`-count one: `Z 0 / d_K(X 1)`. -/
abbrev KH1 := Z 0 ⧸ LinearMap.range (B.dKX 0)

theorem range_dKY_le : LinearMap.range (B.dKY 0) ≤
    (LinearMap.range (B.dKX 0)).comap (B.dCEX 0) := by
  rintro _ ⟨y, rfl⟩
  refine ⟨-(B.dCEY 0 y), ?_⟩
  rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]
  exact B.rel_YZ 0 y

/-- **The induced map** `d̄_CE : H₀^K(row 0) → H₀^K(row 1)`. -/
def dbar : B.KH0 →ₗ[R] B.KH1 :=
  (LinearMap.range (B.dKY 0)).mapQ (LinearMap.range (B.dKX 0)) (B.dCEX 0) B.range_dKY_le

@[simp] theorem dbar_mk (x : X 0) :
    B.dbar (Submodule.Quotient.mk x) = Submodule.Quotient.mk (B.dCEX 0 x) := rfl

/-! ### The comparison map -/

/-- A total cycle gives a `d̄_CE`-cycle of the Koszul row by taking its `p = 0` component. -/
def cyclesToKer : B.cycles →ₗ[R] LinearMap.ker B.dbar where
  toFun x := ⟨Submodule.Quotient.mk ((x : ∀ p, X p) 0), by
    have hx : B.D0 x 0 = 0 := by rw [show B.D0 x = 0 from x.2]; rfl
    rw [D0_apply] at hx
    rw [LinearMap.mem_ker, dbar_mk, Submodule.Quotient.mk_eq_zero]
    exact ⟨-((x : ∀ p, X p) 1), by rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]; exact hx⟩⟩
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

theorem boundaries_le_ker : B.boundaries ≤ LinearMap.ker B.cyclesToKer := by
  rintro x ⟨y, hy⟩
  rw [LinearMap.mem_ker]
  ext
  change Submodule.Quotient.mk ((x : ∀ p, X p) 0) = (0 : B.KH0)
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨y 0, congrFun hy 0⟩

/-- **The comparison map** `H⁰(d_K + d_CE) → ker d̄_CE`. -/
def toKer : B.H0 →ₗ[R] LinearMap.ker B.dbar := B.boundaries.liftQ B.cyclesToKer B.boundaries_le_ker

/-! ### Injectivity: the zigzag building a primitive -/

/-- One step of the injectivity zigzag. -/
theorem inj_step (x : ∀ p, X p) (hx : B.D0 x = 0) (p : ℕ) (y : Y p)
    (hy : B.dCEX p (x p - B.dKY p y) = 0) :
    ∃ y' : Y (p + 1), B.dKY (p + 1) y' = x (p + 1) - B.dCEY p y := by
  apply B.exact_X
  have hxp : B.dCEX p (x p) + B.dKX p (x (p + 1)) = 0 := by
    rw [← D0_apply, hx]; rfl
  have h1 := B.rel_YZ p y
  rw [map_sub] at hy ⊢
  calc B.dKX p (x (p + 1)) - B.dKX p (B.dCEY p y)
      = (B.dCEX p (x p) + B.dKX p (x (p + 1))) - (B.dCEX p (B.dKY p y) + B.dKX p (B.dCEY p y))
          - (B.dCEX p (x p) - B.dCEX p (B.dKY p y)) := by abel
    _ = 0 := by rw [hxp, h1, hy]; abel

/-- The recursively built primitive, with its invariant. -/
noncomputable def injSeq (x : ∀ p, X p) (hx : B.D0 x = 0) (y0 : Y 0)
    (hy0 : B.dKY 0 y0 = x 0) : (p : ℕ) → {y : Y p // B.dCEX p (x p - B.dKY p y) = 0}
  | 0 => ⟨y0, by rw [hy0, sub_self, map_zero]⟩
  | p + 1 =>
    let prev := injSeq x hx y0 hy0 p
    let h := B.inj_step x hx p prev.1 prev.2
    ⟨h.choose, by
      rw [h.choose_spec, sub_sub_cancel]
      exact B.rel_YY p prev.1⟩

theorem injSeq_spec (x : ∀ p, X p) (hx : B.D0 x = 0) (y0 : Y 0) (hy0 : B.dKY 0 y0 = x 0)
    (p : ℕ) : B.dKY (p + 1) (B.injSeq x hx y0 hy0 (p + 1)).1 =
      x (p + 1) - B.dCEY p (B.injSeq x hx y0 hy0 p).1 :=
  (B.inj_step x hx p _ (B.injSeq x hx y0 hy0 p).2).choose_spec

/-- **Collapse, injectivity half.** A total cycle whose `p = 0` component is Koszul-exact
is a total boundary. -/
theorem exists_primitive (x : ∀ p, X p) (hx : B.D0 x = 0) (h0 : x 0 ∈ LinearMap.range (B.dKY 0)) :
    ∃ y, B.Dm y = x := by
  obtain ⟨y0, hy0⟩ := h0
  refine ⟨fun p => (B.injSeq x hx y0 hy0 p).1, ?_⟩
  funext p
  rcases p with _ | p
  · exact hy0
  · rw [Dm_succ]
    rw [B.injSeq_spec, sub_add_cancel]

theorem toKer_injective : Function.Injective B.toKer := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  induction c using Submodule.Quotient.induction_on with
  | H x =>
    have hx0 : Submodule.Quotient.mk ((x : ∀ p, X p) 0) = (0 : B.KH0) := by
      have := congrArg Subtype.val hc
      exact this
    rw [Submodule.Quotient.mk_eq_zero] at hx0
    rw [Submodule.Quotient.mk_eq_zero]
    exact B.exists_primitive x x.2 hx0

/-! ### Surjectivity: the zigzag building a total cycle -/

/-- One step of the surjectivity zigzag. -/
theorem surj_step (p : ℕ) (x : X p) (x' : X (p + 1)) (h : B.dCEX p x + B.dKX p x' = 0) :
    ∃ x'' : X (p + 2), B.dCEX (p + 1) x' + B.dKX (p + 1) x'' = 0 := by
  obtain ⟨x'', hx''⟩ := B.exact_Z p (-(B.dCEX (p + 1) x')) (by
    rw [map_neg, neg_eq_zero]
    have h1 := B.rel_XG p x'
    have h2 : B.dKX p x' = -(B.dCEX p x) := eq_neg_of_add_eq_zero_right h
    rw [h2, map_neg, B.rel_CC, neg_zero, add_zero] at h1
    exact h1)
  exact ⟨x'', by rw [hx'', add_neg_cancel]⟩

/-- The recursively built total cycle: consecutive pairs `(x_p, x_{p+1})`. -/
noncomputable def surjSeq (x0 : X 0) (x1 : X 1) (h01 : B.dCEX 0 x0 + B.dKX 0 x1 = 0) :
    (p : ℕ) → {q : X p × X (p + 1) // B.dCEX p q.1 + B.dKX p q.2 = 0}
  | 0 => ⟨(x0, x1), h01⟩
  | p + 1 =>
    let prev := surjSeq x0 x1 h01 p
    let h := B.surj_step p prev.1.1 prev.1.2 prev.2
    ⟨(prev.1.2, h.choose), h.choose_spec⟩

theorem surjSeq_fst_succ (x0 : X 0) (x1 : X 1) (h01 : B.dCEX 0 x0 + B.dKX 0 x1 = 0) (p : ℕ) :
    (B.surjSeq x0 x1 h01 (p + 1)).1.1 = (B.surjSeq x0 x1 h01 p).1.2 := rfl

/-- **Collapse, surjectivity half.** Every `d̄_CE`-cycle of the Koszul row lifts to a total
cycle. -/
theorem exists_cycle (x0 : X 0) (h : B.dCEX 0 x0 ∈ LinearMap.range (B.dKX 0)) :
    ∃ x : ∀ p, X p, B.D0 x = 0 ∧ x 0 = x0 := by
  obtain ⟨x1, hx1⟩ := h
  have h01 : B.dCEX 0 x0 + B.dKX 0 (-x1) = 0 := by rw [map_neg, hx1, add_neg_cancel]
  refine ⟨fun p => (B.surjSeq x0 (-x1) h01 p).1.1, ?_, rfl⟩
  funext p
  rw [D0_apply]
  change B.dCEX p (B.surjSeq x0 (-x1) h01 p).1.1 +
    B.dKX p (B.surjSeq x0 (-x1) h01 (p + 1)).1.1 = 0
  rw [surjSeq_fst_succ]
  exact (B.surjSeq x0 (-x1) h01 p).2

theorem toKer_surjective : Function.Surjective B.toKer := by
  rintro ⟨c, hc⟩
  induction c using Submodule.Quotient.induction_on with
  | H x0 =>
    rw [LinearMap.mem_ker, dbar_mk, Submodule.Quotient.mk_eq_zero] at hc
    obtain ⟨x, hx, hx0⟩ := B.exists_cycle x0 hc
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    ext
    change Submodule.Quotient.mk (x 0) = _
    rw [hx0]

/-- **Collapse of the `c`-count spectral sequence onto the Koszul row.** Under Koszul
exactness in positive antighost degree, the ghost-number-zero cohomology of
`d_K + d_CE` is the kernel of the induced Chevalley–Eilenberg map on Koszul `H₀`. -/
noncomputable def equivKer : B.H0 ≃ₗ[R] LinearMap.ker B.dbar :=
  LinearEquiv.ofBijective B.toKer ⟨B.toKer_injective, B.toKer_surjective⟩

end LeadingBicomplex

end VOA.LeadingKoszul
