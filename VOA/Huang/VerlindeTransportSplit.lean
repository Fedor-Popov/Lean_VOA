/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.VerlindeEigenMatrix
import VOA.Huang.PentagonCloseEdges

/-!
# Splitting Huang's Cor. 4.7 into a genus-one and a genus-zero input

Y.-Z. Huang, *Vertex operator algebras and the Verlinde conjecture*, Commun. Contemp. Math. 10
(2008), arXiv:math/0406291. `HuangTransportInput` (Cor. 4.7 in the convention of Prop. 4.5) is
split here into

* **(G1)** `VacuumChannelTransportInput` — the genus-one content: the vacuum-channel two-point
  functions `Ψ_x` are `S`-covariant with matrix `D.repS`, the A-cycle acts diagonally on them
  modulo the other channels, and the B-cycle acts by the matrix `transferMatrix c β`, so that
  (Prop. 4.5) `S·β = diag(Ω)·S`. The B-cycle matrix is **not** an unknown: it is a concrete
  genus-zero quantity built in the monoidal category of ordinary modules from the actual
  associator `evalAssoc F H` (`bTransfer`);
* **(G0)** `GenusZeroTransferInput` — the genus-zero content replacing Huang's Thm 4.1 / (4.9):
  `transferMatrix c β x z = s · N_{b x}^{z}` (`TransferTraceInput`), and the genus-zero choices
  exist (`TransferChoiceExists`).

Both are proved to give `FusionEigenInput` (with the proved `RhoNegOneInput`), and hence
`HuangTransportInput` (`huangTransportInput_of_split`). `GenusZeroTransferInput` is proved for every
nice `W` in `VOA.Huang.VerlindeTransportGenusZero`.

## How `bTransfer` arises (the B-cycle, Huang Lemma 4.2 (4.11), Cor. 4.4 (4.24))

Fix `a` and its conjugate `b = a'`; `ε : M_a ⊠ M_b → V` (Huang's `Y^e_{a a'}`) and
`η : V → M_b ⊠ M_a` (the vacuum summand of `M_b ⊠ M_a`) are nonzero. The vacuum channel of the
two-point function traced over `M_x` is the iterate `(M_a ⊠ M_b) ⊠ M_x → V ⊠ M_x → M_x`; through the
associator it is the product `ψ_x = α⁻¹ ≫ (ε ▷ M_x) ≫ λ` (`vacuumProduct`), and decomposing
`M_b ⊠ M_x = ⊕_j M_{lab j}` (`inc`, `proj`) writes `Ψ_x = Σ_j Tr_{M_x} μ_j(w_a, z₁) ν_j(w_b, z₂)`
with `ν_j = proj_j`, `μ_j = (M_a ◁ inc_j) ≫ ψ_x`. Along the B-cycle `z₂ ↦ z₂ + τ`, `q^{L(0)}`
conjugation and cyclicity of the trace turn the trace over `M_x` into the trace over `M_{lab j}` of
the reversed product `ν_j ∘ (M_b ◁ μ_j)`. Its vacuum-channel coefficient is read off by
precomposing the associator and `η ▷ –`: this is `bTransfer F H c x j`, an endomorphism of the
simple `M_{lab j}`, i.e. a scalar `β x j`. Summing the traces over `M_z` gives the B-matrix entry
`transferMatrix c β x z = Σ_{lab j = z} β x j`, up to one constant depending on `a` only
(the normalisations of `ε`, `η` and the skew-symmetry phase relating `Y^e_{a' a}` to `Y^e_{a a'}`),
which is absorbed into `Ω`. Huang writes the same entry as (4.24), a trace of products of fusing
matrices involving `σ₁₂₃`; here no basis and no `S₃`-action is needed.

## Status
No `sorry`, no new axioms. Nothing in this file uses `VOA.pbw`.
-/

noncomputable section

namespace VOA.Huang.VerlindeTransport

open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeFusion
  VOA.Huang.VerlindeEigen VOA.Huang.VerlindeEigenMatrix VOA.Huang.VerlindeVacuum
  VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory Matrix

universe u w v

/-! ## §1 The genus-zero B-cycle transfer -/

section Defs

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- A member of a modular-data family as an object of the category of ordinary modules. -/
def famObj (D : VOA.ModularData W ι) (x : ι) : Ordinary W := Ordinary.of (D.Mfam x).isMod

/-- The genus-zero choices entering the B-cycle transport of the vacuum channel of
`M_a ⊠ M_b`: a nonzero `ε : M_a ⊠ M_b → V` (Huang's `Y^e_{a a'}`), a nonzero
`η : V → M_b ⊠ M_a`, and for every traced label `x` a finite split presentation of `M_b ⊠ M_x` by
family members (`Σ_j proj_j ≫ inc_j = 𝟙`; repeated labels allowed). A choice exists only when
`b ≅ a'` (`ε ≠ 0`). -/
structure TransferChoice (F : FusionChoice W) (D : VOA.ModularData W ι) (a b : ι) where
  /-- Huang's `Y^e_{a a'}`, as a morphism into the unit. -/
  ε : tensorObj F (famObj D a) (famObj D b) ⟶ vacuumObject
  ε_ne : ε ≠ 0
  /-- The vacuum summand of `M_b ⊠ M_a`. -/
  η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)
  η_ne : η ≠ 0
  /-- Number of summands of `M_b ⊠ M_x`. -/
  r : ι → ℕ
  /-- Their labels. -/
  lab : ∀ x, Fin (r x) → ι
  /-- Inclusions. -/
  inc : ∀ x j, famObj D (lab x j) ⟶ tensorObj F (famObj D b) (famObj D x)
  /-- Projections. -/
  proj : ∀ x j, tensorObj F (famObj D b) (famObj D x) ⟶ famObj D (lab x j)
  /-- The presentation is split. -/
  total : ∀ x, ∑ j, proj x j ≫ inc x j = 𝟙 (tensorObj F (famObj D b) (famObj D x))

/-- The B-cycle matrix: the entry `x → z` collects the summands of `M_b ⊠ M_x` labelled `z`. -/
def transferMatrix {F : FusionChoice W} {D : VOA.ModularData W ι} {a b : ι}
    (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ) (x z : ι) : ℂ :=
  ∑ j, if c.lab x j = z then β x j else 0

variable (F : FusionChoice W) (H : OrdinaryFourPointInput F) {D : VOA.ModularData W ι} {a b : ι}

/-- The vacuum channel at traced label `x`, in product form:
`ψ_x = α⁻¹ ≫ (ε ▷ M_x) ≫ λ : M_a ⊠ (M_b ⊠ M_x) → M_x`. -/
def vacuumProduct (c : TransferChoice F D a b) (x : ι) :
    tensorObj F (famObj D a) (tensorObj F (famObj D b) (famObj D x)) ⟶ famObj D x :=
  (evalAssoc F H (famObj D a) (famObj D b) (famObj D x)).inv ≫
    tensorHom F c.ε (𝟙 (famObj D x)) ≫ (leftUnitor F (famObj D x)).hom

/-- **The B-cycle transfer** at traced label `x` and summand `j`: the vacuum-channel coefficient of
the reversed product `proj_j ∘ (M_b ◁ μ_j)`, `μ_j = (M_a ◁ inc_j) ≫ ψ_x`, as an endomorphism of
`M_{lab j}`. -/
def bTransfer (c : TransferChoice F D a b) (x : ι) (j : Fin (c.r x)) :
    famObj D (c.lab x j) ⟶ famObj D (c.lab x j) :=
  (leftUnitor F (famObj D (c.lab x j))).inv ≫ tensorHom F c.η (𝟙 (famObj D (c.lab x j))) ≫
    (evalAssoc F H (famObj D b) (famObj D a) (famObj D (c.lab x j))).hom ≫
    tensorHom F (𝟙 (famObj D b))
      (tensorHom F (𝟙 (famObj D a)) (c.inc x j) ≫ vacuumProduct F H c x) ≫ c.proj x j

/-- `β` lists the scalars of the transfers (Schur: each `bTransfer` is a scalar). -/
def IsTransferScalar (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ) : Prop :=
  ∀ x j, bTransfer F H c x j = β x j • 𝟙 (famObj D (c.lab x j))


end Defs

/-! ## §2 The two named inputs -/

/-- **(G1) Genus one: Huang Prop. 4.5 for the vacuum-channel two-point functions, with the
B-cycle matrix of Lemma 4.2 (4.11) / Cor. 4.4 (4.24) in categorical form.**

For a nice `W`, a complete irredundant family `D` with Zhu modular data, any choice of fusion
products `F` (with the proved four-point input `H`), labels `a, b` and genus-zero choices `c`
(which force `b ≅ a'`), and the scalars `β` of the B-cycle transfers: there are A-cycle
eigenvalues `Ω` with `Ω_{v0} ≠ 0` such that `S · β = diag(Ω) · S`, where `S = D.repS` and
`β_{yz} = transferMatrix c β y z`.

*What it says, in Huang's terms.* `Ψ_x = E Tr_{M_x} Y_{M_x}(U(e^{2πiz₂}) Y^e_{a a'}(w_a, z₁−z₂)
w_{a'}, e^{2πiz₂}) q^{L(0)−c/24}` (§2, (2.5)–(2.8)). Then (i) `S(Ψ_x) = Σ_y S_xy Ψ_y` (the
"clearly" before Thm 4.6: termwise Zhu modularity of the one-point functions of the `V`-components
of `Y^e_{a a'}(w_a, z) w_{a'}`); (ii) the A-cycle `z₂ ↦ z₂ − 1` acts on `Ψ_x` by `Ω_x` modulo the
non-vacuum channels (Lemma 4.2 (4.10), Cor. 4.4 (4.23), `Ω_x = (B^{(−1)})²`, `Ω_{v0} = 1` up to a
common factor); (iii) the B-cycle `z₂ ↦ z₂ + τ` acts by `Σ_z β_xz Ψ_z` modulo the non-vacuum
channels, with `β_xz` a fixed nonzero multiple (depending on `a` only) of
`transferMatrix c β x z` (Lemma 4.2 (4.11): product channel, `q^{L(0)}` conjugation, trace
cyclicity, return to the iterate channel; see the module docstring); (iv) Prop. 2.11 (independence
of the iterate channels) and Prop. 4.5 (`βS = Sα`, the rescaling `z ↦ z/τ`). The deduction from
(i)–(iv) is `VerlindeEigenMatrix.transport_conj` (`vacuumChannelTransport_of_functions` below).

*Truth.* By (i)–(iv), Huang 2008 §§2–4 (convergence and continuation from Huang 2005 and Huang's
genus-one papers). Independently of that derivation, it is machine-checked
(`VerlindeTransportHeadline.vacuumChannelTransportInput_iff`) that, given the proved genus zero and
`ρ(−1) = C`, this Prop is equivalent to `FusionEigenInput ∧ ZigzagNonzeroInput` — Huang's Thm 5.2
and the categorical form of his Prop. 5.1 (a consequence of rigidity, Huang 2008b) — so it is TRUE
and NOT narrower than `FusionEigenInput`. Non-vacuity: `TransferChoiceExists` (proved for nice
`W`) supplies `c` and `β` for every `b`. -/
def VacuumChannelTransportInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
      ∀ (F : FusionChoice W) (H : OrdinaryFourPointInput F) (a b : ι)
        (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ), IsTransferScalar F H c β →
        ∃ Ω : ι → ℂ, Ω v0 ≠ 0 ∧
          ∀ x z, ∑ y, D.repS x y * transferMatrix c β y z = Ω x * D.repS x z

/-- **(G0a) Genus zero, Huang Thm 4.1 / (4.9) in trace form**: the B-cycle matrix is a constant
multiple of the fusion matrix, `transferMatrix c β x z = s · N_{b x}^{z}`. Proved for nice `W`
(`VerlindeTransportGenusZero.transferTraceInput_pbw`): the transfer factors through the zig-zag
`(λ⁻¹ ≫ (η ▷ M_b) ≫ α ≫ (M_b ◁ ε) ≫ ρ)`, a scalar by Schur, and the remaining sum is the trace of
the identity of `Hom(M_b ⊠ M_x, M_z)`. -/
def TransferTraceInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
      ∀ (F : FusionChoice W) (H : OrdinaryFourPointInput F) (a b : ι)
        (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ), IsTransferScalar F H c β →
        ∃ s : ℂ, ∀ x z, transferMatrix c β x z = s * (famFusion D b x z : ℂ)

/-- **(G0b) Genus zero: the choices exist.** Some fusion choice `F` has the four-point input, and
for every label `b` there are `a`, genus-zero choices `c` and transfer scalars `β`. Proved for nice
`W` (`VerlindeTransportGenusZero.transferChoiceExists_pbw`; `a = b'`). -/
def TransferChoiceExists : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
      ∃ (F : FusionChoice W) (H : OrdinaryFourPointInput F), ∀ b : ι,
        ∃ (a : ι) (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ),
          IsTransferScalar F H c β

/-- **(G0) The genus-zero input** of the split. -/
def GenusZeroTransferInput : Prop := TransferTraceInput.{u, w} ∧ TransferChoiceExists.{u, w}

/-! ## §3 The abstract bridge to (G1) (for the genus-one argument) -/

/-- (G1)'s conclusion from Huang's genus-one data on any space of functions: an `S`-operator, the
A- and B-transports and an `S`-stable remainder (non-vacuum channels), vacuum-channel functions
`Ψ_x` independent modulo it, `S(Ψ_x) = Σ_y S_xy Ψ_y`, `T_B ∘ S = S ∘ T_A` on the `Ψ_x`, A-cycle
eigenvalues `Ω`, and B-cycle matrix `κ · transferMatrix` (`κ ≠ 0` a normalisation constant). This
is exactly the shape the genus-one argument must produce, with `K` the actual two-point
functions. -/
theorem vacuumChannelTransport_of_functions {ι : Type w} [Fintype ι] {K : Type v}
    [AddCommGroup K] [Module ℂ K] (R : Submodule ℂ K) (Sop tA tB : K →ₗ[ℂ] K) (Ψ : ι → K)
    (S B : ι → ι → ℂ) (Ω : ι → ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (hSR : ∀ r ∈ R, Sop r ∈ R)
    (hS : ∀ x, Sop (Ψ x) = ∑ y, S x y • Ψ y)
    (hcomm : ∀ x, tB (Sop (Ψ x)) = Sop (tA (Ψ x)))
    (hA : ∀ x, tA (Ψ x) - Ω x • Ψ x ∈ R)
    (hB : ∀ x, tB (Ψ x) - ∑ z, (κ * B x z) • Ψ z ∈ R)
    (hind : ∀ c : ι → ℂ, ∑ z, c z • Ψ z ∈ R → c = 0) (x z : ι) :
    ∑ y, S x y * B y z = (Ω x / κ) * S x z := by
  have h := transport_conj R Sop tA tB Ψ S (fun x z => κ * B x z) Ω hSR hS hcomm hA hB hind x z
  have h' : κ * ∑ y, S x y * B y z = Ω x * S x z := by
    rw [← h, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  field_simp
  linear_combination h'

/-! ## §4 The reductions -/

section Reduction

/-- The charge-conjugation set-up of `fusionEigenInput_of_transport_rho`, extracted: from
`ρ(−1) = C` one gets an involution `σ` and the two-sided inverse `T = S·P_σ` of `S`. -/
theorem rho_setup (hR : RhoNegOneInput.{u, w}) {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (hNice : Nice W) {ι : Type w} [Fintype ι] [DecidableEq ι]
    (D : VOA.ModularData W ι) (hZ : ZhuModularityAnalytic D) (hirr : Irredundant D.Mfam)
    (hcomp : Complete D.Mfam) (v0 : ι)
    (hv0 : Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W))) :
    ∃ (σ : ι → ι) (T : Matrix ι ι ℂ), (∀ x, σ (σ x) = x) ∧
      T * Matrix.of D.repS = 1 ∧ Matrix.of D.repS * T = 1 ∧
      (∀ y z, T y (σ z) = D.repS y z) ∧
      (∀ a b, famFusion D a b v0 = if b = σ a then 1 else 0) ∧
      (∀ x z, D.repS (σ x) (σ z) = D.repS x z) := by
  obtain ⟨σ, hP, hdual⟩ :=
    chargeConjugationInput_of_rhoNegOne hR 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  set T : Matrix ι ι ℂ := D.rep (ModularGroup.S * -1) with hTdef'
  have hRS : D.rep ModularGroup.S = Matrix.of D.repS := D.rep_S
  have hST : Matrix.of D.repS * T = 1 := by
    rw [← hRS, hTdef', ← map_mul, ← mul_assoc, modularS_mul_S, neg_one_mul, neg_neg, map_one]
  have hTS : T * Matrix.of D.repS = 1 := mul_eq_one_comm.mp hST
  have hTval : ∀ x y, T x y = ∑ u, D.repS x u * (if y = σ u then 1 else 0) := by
    intro x y
    rw [hTdef', map_mul, hRS, Matrix.mul_apply]
    simp only [Matrix.of_apply, hP]
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    have h1 : D.rep (-1) * D.rep (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    have h2 := congrFun (congrFun h1 x) x
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h2
    simp only [hP] at h2
    rw [Finset.sum_eq_single (σ x)] at h2
    · by_contra hne
      rw [if_pos rfl, if_neg (Ne.symm hne), mul_zero] at h2
      exact zero_ne_one h2
    · intro u _ hu; rw [if_neg hu, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hσinj : Function.Injective σ := fun x y hxy => by rw [← hσσ x, hxy, hσσ y]
  have hTσ : ∀ y z, T y (σ z) = D.repS y z := by
    intro y z
    rw [hTval, Finset.sum_eq_single z]
    · simp
    · intro u _ hu
      rw [if_neg (fun h => hu (hσinj h).symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ z) h
  have hSσ : ∀ x z, D.repS (σ x) (σ z) = D.repS x z := by
    intro x z
    have hc : D.rep (-1) * D.rep ModularGroup.S = D.rep ModularGroup.S * D.rep (-1) := by
      rw [← map_mul, ← map_mul, neg_one_mul, mul_neg_one]
    have h := congrFun (congrFun hc x) (σ z)
    rw [Matrix.mul_apply, Matrix.mul_apply, hRS] at h
    simp only [hP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [h, Finset.sum_eq_single z]
    · simp
    · intro u _ hu
      rw [if_neg (fun h => hu (hσinj h).symm)]
    · intro h; exact absurd (Finset.mem_univ z) h
  exact ⟨σ, T, hσσ, hTS, hST, hTσ, hdual, hSσ⟩

/-- **(G1) + (G0) + `ρ(−1) = C` give Huang's Thm 5.2.** For each `b`, (G0b) supplies `a`, `c`,
`β`; (G1) gives `S·β = diag(Ω)·S`; (G0a) gives `β = s·N(b)`; the row form of Thm 5.2
(`fusionEigen_of_row`, with `S⁻¹ = S·P_σ`) concludes. -/
theorem fusionEigenInput_of_split (h1 : VacuumChannelTransportInput.{u, w})
    (h0 : GenusZeroTransferInput.{u, w}) (hR : RhoNegOneInput.{u, w}) :
    FusionEigenInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0
  obtain ⟨σ, T, -, hTS, hST, hTσ, -, -⟩ := rho_setup hR hNice D hZ hirr hcomp v0 hv0
  obtain ⟨F, H, hch⟩ := h0.2 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  refine fusionEigen_of_row (v0 := v0) σ T hTS hST hTσ (fun b => ?_)
  obtain ⟨a, c, β, hβ⟩ := hch b
  obtain ⟨Ω, hΩ, hrow⟩ := h1 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c β hβ
  obtain ⟨s, hs⟩ := h0.1 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c β hβ
  refine ⟨Ω, s, hΩ, fun x z => ?_⟩
  rw [← hrow x z]
  exact Finset.sum_congr rfl (fun y _ => by rw [hs])

/-- **Thm 5.2 and `ρ(−1) = C` give Cor. 4.7 in the Prop. 4.5 convention** (`Ω = λ`, `f = 1`),
using the FHL symmetry `N_{ay}^x = N_{a,σx}^{σy}`. Together with `fusionEigenInput_of_transport_rho`
this certifies that `HuangTransportInput` and `FusionEigenInput` have equal strength given
`RhoNegOneInput`. -/
theorem huangTransportInput_of_eigen_rho (hE : FusionEigenInput.{u, w})
    (hR : RhoNegOneInput.{u, w}) : HuangTransportInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 a
  obtain ⟨σ, T, hσσ, hTS, hST, hTσ, hdual, -⟩ := rho_setup hR hNice D hZ hirr hcomp v0 hv0
  have hσinj : Function.Injective σ := fun x y hxy => by rw [← hσσ x, hxy, hσσ y]
  have hσbij : Function.Bijective σ := ⟨hσinj, fun x => ⟨σ x, hσσ x⟩⟩
  have hsym : ∀ a x y, famFusion D a y x = famFusion D a (σ x) (σ y) :=
    famFusion_atrans_sigma D hNice σ (contra_equiv_of_vacuum D hNice v0 hv0 σ hdual)
  have hEig := hE 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  obtain ⟨hne, hsymm, -⟩ :=
    huangVerlindeFusionInput_of_eigen_rho hE hR 𝒱 W hNice ι D hZ hirr hcomp v0 hv0
  have hunit := famFusion_vac_right D hirr v0 hv0
  refine ⟨fun z => eigval hEig a z, 1, ?_, fun x z => ?_⟩
  · intro h0
    have h := eq_eigval_mul hunit hEig a v0
    simp only at h0
    rw [h0, zero_mul, ← hsymm a] at h
    exact hne a h
  -- matrices
  set Nm : Matrix ι ι ℂ := Matrix.of fun x y => (famFusion D a x y : ℂ) with hNm
  set Sm : Matrix ι ι ℂ := Matrix.of D.repS with hSm
  have hNS : Nm * Sm = Sm * Matrix.diagonal (fun z => eigval hEig a z) := by
    ext x' z'
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [hNm, hSm, Matrix.of_apply]
    rw [eigval_spec hEig a z' x', mul_comm]
  have key : T * Nm = Matrix.diagonal (fun z => eigval hEig a z) * T := by
    calc T * Nm = T * Nm * (Sm * T) := by rw [hST, Matrix.mul_one]
      _ = T * (Nm * Sm) * T := by simp only [Matrix.mul_assoc]
      _ = T * (Sm * Matrix.diagonal (fun z => eigval hEig a z)) * T := by rw [hNS]
      _ = (T * Sm) * Matrix.diagonal (fun z => eigval hEig a z) * T := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal (fun z => eigval hEig a z) * T := by rw [hTS, Matrix.one_mul]
  have hkey := congrFun (congrFun key x) (σ z)
  rw [Matrix.mul_apply, Matrix.diagonal_mul, hTσ] at hkey
  simp only [hNm, Matrix.of_apply] at hkey
  -- reindex the transport sum by `y = σ u`
  have hTS' : ∀ u, D.repS x (σ u) = T x u := fun u => by rw [← hTσ x (σ u), hσσ]
  have hre : ∑ y, D.repS x y * (1 * (famFusion D a z y : ℂ))
      = ∑ u, T x u * (famFusion D a u (σ z) : ℂ) := by
    rw [← Equiv.sum_comp (Equiv.ofBijective σ hσbij)]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    simp only [Equiv.ofBijective_apply, one_mul]
    rw [hTS', hsym a (σ u) z, hσσ]
  rw [hre, hkey]

/-- **`huangTransportInput_of_split`**: (G1) and (G0), with the proved-elsewhere
`RhoNegOneInput`, give `HuangTransportInput` (Huang Cor. 4.7). -/
theorem huangTransportInput_of_split (h1 : VacuumChannelTransportInput.{u, w})
    (h0 : GenusZeroTransferInput.{u, w}) (hR : RhoNegOneInput.{u, w}) :
    HuangTransportInput.{u, w} :=
  huangTransportInput_of_eigen_rho (fusionEigenInput_of_split h1 h0 hR) hR

end Reduction

end VOA.Huang.VerlindeTransport
