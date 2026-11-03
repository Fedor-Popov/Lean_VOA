/-
Copyright (c) 2026 Leonardo Rastelli and Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.LatticesAndCodes.Construction.CodeToLattice
import VOA.LatticesAndCodes.Codes.GolayEnumerator
import VOA.LatticesAndCodes.Lattice.Index

/-!
# The Leech lattice

**Ebeling §2.8.**  Inside `Γ_Golay = ρ⁻¹(Golay) ⊆ ℤ²⁴` with the halved form (convention **S3**)
let `α(x) = (∑ᵢ xᵢ)/2 mod 2`; it is a homomorphism, its kernel `A` has index `2`, and

`Λ = A ∪ ((½·1) + N)`,  `N = Γ_Golay \ A`,

is the Leech lattice.  Doubling to clear the `½`, the carrier used here is

`M = 2A ∪ (u + 2A) ⊆ ℤ²⁴`,  `u = (5,1,1,…,1) = 1 + 2·(2e₀)`,

with the form `⟪x,y⟫ = (∑ᵢ xᵢ yᵢ)/8`, which is `Λ`'s form transported along `x ↦ 2x`.

## The determinant

`det Λ = 1` is the index–determinant relation (`IntegralLattice.det_of_injective`) applied twice
to the *same* lattice `A`:

* `a ↦ a` embeds `A` in `Γ_Golay` with index `2`, so `det A = 4·det Γ_Golay = 4`;
* `a ↦ 2a` embeds `A` in `Λ` with index `2` — and it is form-preserving, because doubling the
  vectors multiplies the dot product by `4` while the form is divided by `8` instead of `2` — so
  `det A = 4·det Λ`.

Hence `det Λ = 1`.  No index computation inside `ℤ²⁴` is needed.

## Main definitions and results

* `Leech.lattice` — the Leech lattice as an `IntegralLattice`.
* `Leech.lattice_rank`, `Leech.lattice_isEven`, `Leech.lattice_isPosDef`,
  `Leech.lattice_isUnimodular`, `Leech.lattice_no_roots`.

## References

Ebeling, *Lattices and Codes*, §2.8.
-/

open scoped Matrix
open Module (finrank finBasis)

noncomputable section

namespace IntegralLattice

/-- The lattice with carrier a submodule `N ⊆ ℤⁿ` and form `⟪x,y⟫ = (∑ᵢ xᵢyᵢ)/d`.  This is the
shape of `latticeOfCode` (where `d = 2`) and of the Leech lattice (where `d = 8`). -/
def dotLattice {n : ℕ} (d : ℤ) (N : Submodule ℤ (Fin n → ℤ))
    (hdvd : ∀ x ∈ N, ∀ y ∈ N, d ∣ (x ⬝ᵥ y)) : IntegralLattice where
  carrier := ↥N
  bilin := LinearMap.mk₂ ℤ
    (fun x y => ((x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ)) / d)
    (fun x₁ x₂ y => by
      simp only [Submodule.coe_add, add_dotProduct]
      exact Int.add_ediv_of_dvd_left (hdvd _ x₁.2 _ y.2))
    (fun c x y => by
      simp only [Submodule.coe_smul, smul_dotProduct, smul_eq_mul]
      rw [Int.mul_ediv_assoc _ (hdvd _ x.2 _ y.2)])
    (fun x y₁ y₂ => by
      simp only [Submodule.coe_add, dotProduct_add]
      exact Int.add_ediv_of_dvd_left (hdvd _ x.2 _ y₁.2))
    (fun c x y => by
      simp only [Submodule.coe_smul, dotProduct_smul, smul_eq_mul]
      rw [Int.mul_ediv_assoc _ (hdvd _ x.2 _ y.2)])
  bilin_symm x y := by
    show ((x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ)) / d = ((y : Fin n → ℤ) ⬝ᵥ (x : Fin n → ℤ)) / d
    rw [dotProduct_comm]

@[simp] theorem dotLattice_bilin {n : ℕ} (d : ℤ) (N : Submodule ℤ (Fin n → ℤ))
    (hdvd : ∀ x ∈ N, ∀ y ∈ N, d ∣ (x ⬝ᵥ y)) (x y : N) :
    (dotLattice d N hdvd).bilin x y = ((x : Fin n → ℤ) ⬝ᵥ (y : Fin n → ℤ)) / d := rfl

end IntegralLattice

namespace Leech

open Code IntegralLattice

/-! ### The lattice of the Golay code and its parity sublattice -/

/-- `ρ⁻¹(Golay) ⊆ ℤ²⁴`. -/
def preG : Submodule ℤ (Fin 24 → ℤ) := preimageOfCode Code.golay

theorem mem_preG {x : Fin 24 → ℤ} : x ∈ preG ↔ reduceMod 2 24 x ∈ Code.golay := Iff.rfl

/-- The Golay code is contained in its dual, with the *type* `golay ≤ golay.dual` rather than
`IsSelfOrthogonal`, which is a `def` and blocks later rewriting. -/
theorem golay_le_dual : Code.golay ≤ Code.golay.dual := Code.golay_isSelfOrthogonal

/-- `Γ_Golay`, the lattice of the Golay code. -/
def golayLattice : IntegralLattice := latticeOfCode Code.golay golay_le_dual

theorem golayLattice_det : golayLattice.det = 1 := by
  rw [golayLattice, latticeOfCode_det, Code.golay_rank]
  norm_num

theorem golayLattice_rank : golayLattice.rank = 24 := by
  rw [golayLattice, latticeOfCode_rank]

theorem two_dvd_dot {x y : Fin 24 → ℤ} (hx : x ∈ preG) (hy : y ∈ preG) : (2 : ℤ) ∣ x ⬝ᵥ y :=
  two_dvd_dotProduct_of_mem golay_le_dual hx hy

theorem four_dvd_dot_self {x : Fin 24 → ℤ} (hx : x ∈ preG) : (4 : ℤ) ∣ x ⬝ᵥ x := by
  have heven : (latticeOfCode Code.golay golay_le_dual).IsEven :=
    (latticeOfCode_isEven Code.golay golay_le_dual).mpr Code.golay_isDoublyEven
  have h : (2 : ℤ) ∣ (latticeOfCode Code.golay golay_le_dual).bilin ⟨x, hx⟩ ⟨x, hx⟩ :=
    heven ⟨x, hx⟩
  rw [latticeOfCode_bilin] at h
  simp only at h
  obtain ⟨m, hm⟩ := two_dvd_dot hx hx
  rw [hm, Int.mul_ediv_cancel_left _ (by norm_num : (2:ℤ) ≠ 0)] at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hm, hk]; ring⟩

theorem two_dvd_sum {x : Fin 24 → ℤ} (hx : x ∈ preG) : (2 : ℤ) ∣ ∑ i, x i := by
  have hw : (4 : ℕ) ∣ Code.weight (reduceMod 2 24 x) :=
    Code.golay_isDoublyEven _ (mem_preG.mp hx)
  have hsum : ((Code.weight (reduceMod 2 24 x) : ℕ) : ℤ)
      = ∑ i, if (2 : ℤ) ∣ x i then (0 : ℤ) else 1 := weight_reduceMod_eq_sum x
  have hdiff : (2 : ℤ) ∣ ∑ i, (x i - if (2 : ℤ) ∣ x i then (0 : ℤ) else 1) := by
    refine Finset.dvd_sum fun i _ => ?_
    by_cases h : (2 : ℤ) ∣ x i
    · simp [h]
    · simp only [h, if_false]
      omega
  rw [Finset.sum_sub_distrib, ← hsum] at hdiff
  have h2 : (2 : ℤ) ∣ ((Code.weight (reduceMod 2 24 x) : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := hw
    exact ⟨2 * k, by rw [hk]; push_cast; ring⟩
  omega

/-- Ebeling's index-2 sublattice: the vectors of `ρ⁻¹(Golay)` with `4 ∣ ∑ᵢ xᵢ`. -/
def subA : Submodule ℤ (Fin 24 → ℤ) where
  carrier := {x | x ∈ preG ∧ (4 : ℤ) ∣ ∑ i, x i}
  add_mem' {x y} hx hy := by
    refine ⟨preG.add_mem hx.1 hy.1, ?_⟩
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact dvd_add hx.2 hy.2
  zero_mem' := ⟨preG.zero_mem, by simp⟩
  smul_mem' c x hx := by
    refine ⟨preG.smul_mem c hx.1, ?_⟩
    have : ∑ i, (c • x) i = c * ∑ i, x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp
    rw [this]
    exact Dvd.dvd.mul_left hx.2 c

@[simp] theorem mem_subA {x : Fin 24 → ℤ} : x ∈ subA ↔ x ∈ preG ∧ (4 : ℤ) ∣ ∑ i, x i := Iff.rfl

theorem subA_le_preG : subA ≤ preG := fun _ hx => hx.1

/-! ### The Leech carrier -/

/-- `u = (5,1,…,1) = 1 + 2·(2e₀)`.  Its reduction is the all-ones word of the Golay code and
`∑ᵢ uᵢ = 28`, so it lies in `A`; it is the generator of `Λ` over `2A`. -/
def uVec : Fin 24 → ℤ := fun i => if i = 0 then 5 else 1

theorem sum_uVec : ∑ i, uVec i = 28 := by decide +kernel

theorem dot_uVec (a : Fin 24 → ℤ) : a ⬝ᵥ uVec = (∑ i, a i) + 4 * a 0 := by
  rw [dotProduct]
  have hterm : ∀ i : Fin 24, a i * uVec i = a i + (if i = 0 then 4 * a i else 0) := by
    intro i
    by_cases h : i = 0 <;> simp [uVec, h] <;> ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem uVec_mem_preG : uVec ∈ preG := by
  rw [mem_preG]
  have h1 : reduceMod 2 24 uVec = 1 := by
    funext i
    show ((uVec i : ℤ) : ZMod 2) = 1
    by_cases h : i = 0
    · rw [show uVec i = 5 from by simp [uVec, h]]
      decide
    · rw [show uVec i = 1 from by simp [uVec, h]]
      norm_num
  rw [h1]
  exact Code.one_mem_of_isSelfDual_of_isEven Code.golay_isSelfDual
    Code.golay_isDoublyEven.isEven

theorem uVec_mem_subA : uVec ∈ subA := ⟨uVec_mem_preG, by rw [sum_uVec]; norm_num⟩

/-- `2A`. -/
def subA2 : Submodule ℤ (Fin 24 → ℤ) := subA.map ((2 : ℤ) • LinearMap.id)

theorem mem_subA2 {y : Fin 24 → ℤ} : y ∈ subA2 ↔ ∃ a ∈ subA, (2 : ℤ) • a = y := by
  simp [subA2, Submodule.mem_map]

theorem two_smul_mem_subA2 {a : Fin 24 → ℤ} (ha : a ∈ subA) : (2 : ℤ) • a ∈ subA2 :=
  mem_subA2.2 ⟨a, ha, rfl⟩

theorem two_smul_uVec_mem_subA2 : (2 : ℤ) • uVec ∈ subA2 := two_smul_mem_subA2 uVec_mem_subA

/-- The carrier of the Leech lattice, `2A ∪ (u + 2A) ⊆ ℤ²⁴`. -/
def carrier : Submodule ℤ (Fin 24 → ℤ) where
  carrier := {x | x ∈ subA2 ∨ x - uVec ∈ subA2}
  zero_mem' := Or.inl subA2.zero_mem
  add_mem' {x y} hx hy := by
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (subA2.add_mem hx hy)
    · refine Or.inr ?_
      have : x + y - uVec = x + (y - uVec) := by ring
      rw [this]
      exact subA2.add_mem hx hy
    · refine Or.inr ?_
      have : x + y - uVec = (x - uVec) + y := by ring
      rw [this]
      exact subA2.add_mem hx hy
    · refine Or.inl ?_
      have : x + y = ((x - uVec) + (y - uVec)) + (2 : ℤ) • uVec := by
        rw [two_smul]; ring
      rw [this]
      exact subA2.add_mem (subA2.add_mem hx hy) two_smul_uVec_mem_subA2
  smul_mem' c x hx := by
    rcases hx with hx | hx
    · exact Or.inl (subA2.smul_mem c hx)
    · rcases Int.even_or_odd c with ⟨k, hk⟩ | ⟨k, hk⟩
      · subst hk
        refine Or.inl ?_
        have hEq : (k + k) • x = (k + k) • (x - uVec) + k • ((2 : ℤ) • uVec) := by module
        rw [hEq]
        exact subA2.add_mem (subA2.smul_mem _ hx) (subA2.smul_mem k two_smul_uVec_mem_subA2)
      · subst hk
        refine Or.inr ?_
        have hEq : (2 * k + 1) • x - uVec
            = (2 * k + 1) • (x - uVec) + k • ((2 : ℤ) • uVec) := by module
        rw [hEq]
        exact subA2.add_mem (subA2.smul_mem _ hx) (subA2.smul_mem k two_smul_uVec_mem_subA2)

@[simp] theorem mem_carrier {x : Fin 24 → ℤ} :
    x ∈ carrier ↔ x ∈ subA2 ∨ x - uVec ∈ subA2 := Iff.rfl

theorem subA2_le_carrier : subA2 ≤ carrier := fun _ hx => Or.inl hx

/-! ### Integrality of the form -/

theorem dot_two_smul_two_smul (a b : Fin 24 → ℤ) :
    ((2 : ℤ) • a) ⬝ᵥ ((2 : ℤ) • b) = 4 * (a ⬝ᵥ b) := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem eight_dvd_dot_of_subA2 {x y : Fin 24 → ℤ} (hx : x ∈ subA2) (hy : y ∈ subA2) :
    (8 : ℤ) ∣ x ⬝ᵥ y := by
  obtain ⟨a, ha, rfl⟩ := mem_subA2.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_subA2.1 hy
  obtain ⟨m, hm⟩ := two_dvd_dot ha.1 hb.1
  exact ⟨m, by rw [dot_two_smul_two_smul, hm]; ring⟩

theorem eight_dvd_dot_subA2_uVec {x : Fin 24 → ℤ} (hx : x ∈ subA2) : (8 : ℤ) ∣ x ⬝ᵥ uVec := by
  obtain ⟨a, ha, rfl⟩ := mem_subA2.1 hx
  rw [smul_dotProduct, smul_eq_mul, dot_uVec]
  obtain ⟨k, hk⟩ := ha.2
  exact ⟨k + a 0, by rw [hk]; ring⟩

theorem uVec_dot_uVec : uVec ⬝ᵥ uVec = 48 := by decide +kernel

theorem eight_dvd_dot {x y : Fin 24 → ℤ} (hx : x ∈ carrier) (hy : y ∈ carrier) :
    (8 : ℤ) ∣ x ⬝ᵥ y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact eight_dvd_dot_of_subA2 hx hy
  · rw [show x ⬝ᵥ y = x ⬝ᵥ (y - uVec) + x ⬝ᵥ uVec from by rw [dotProduct_sub]; ring]
    exact dvd_add (eight_dvd_dot_of_subA2 hx hy) (eight_dvd_dot_subA2_uVec hx)
  · rw [show x ⬝ᵥ y = (x - uVec) ⬝ᵥ y + uVec ⬝ᵥ y from by rw [sub_dotProduct]; ring]
    refine dvd_add (eight_dvd_dot_of_subA2 hx hy) ?_
    rw [dotProduct_comm]
    exact eight_dvd_dot_subA2_uVec hy
  · rw [show x ⬝ᵥ y = (x - uVec) ⬝ᵥ (y - uVec) + (x - uVec) ⬝ᵥ uVec + uVec ⬝ᵥ (y - uVec)
        + uVec ⬝ᵥ uVec from by simp only [sub_dotProduct, dotProduct_sub]; ring]
    refine dvd_add (dvd_add (dvd_add (eight_dvd_dot_of_subA2 hx hy)
      (eight_dvd_dot_subA2_uVec hx)) ?_) ⟨6, by rw [uVec_dot_uVec]; norm_num⟩
    rw [dotProduct_comm]
    exact eight_dvd_dot_subA2_uVec hy

/-! ### The Leech lattice -/

/-- **The Leech lattice** (Ebeling §2.8): the carrier is `2A ∪ (u + 2A) ⊆ ℤ²⁴` and the form is
`⟪x,y⟫ = (∑ᵢ xᵢyᵢ)/8`. -/
def lattice : IntegralLattice := dotLattice 8 carrier (fun x hx y hy => eight_dvd_dot hx hy)

@[simp] theorem lattice_bilin (x y : carrier) :
    lattice.bilin x y = ((x : Fin 24 → ℤ) ⬝ᵥ (y : Fin 24 → ℤ)) / 8 := rfl

theorem eight_mul_lattice_bilin (x y : carrier) :
    8 * lattice.bilin x y = (x : Fin 24 → ℤ) ⬝ᵥ (y : Fin 24 → ℤ) :=
  Int.mul_ediv_cancel' (eight_dvd_dot x.2 y.2)

/-- The Leech lattice is positive definite. -/
theorem lattice_isPosDef : lattice.IsPosDef := by
  show ∀ x : carrier, x ≠ 0 → 0 < ((x : Fin 24 → ℤ) ⬝ᵥ (x : Fin 24 → ℤ)) / 8
  intro x hx
  have hxne : (x : Fin 24 → ℤ) ≠ 0 := fun h => hx (Subtype.ext h)
  have hpos : 0 < (x : Fin 24 → ℤ) ⬝ᵥ (x : Fin 24 → ℤ) := dotProduct_self_pos hxne
  obtain ⟨k, hk⟩ := eight_dvd_dot x.2 x.2
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  omega

/-- **The Leech lattice is even**: the twist by `u` is exactly what makes the odd coset even. -/
theorem lattice_isEven : lattice.IsEven := by
  show ∀ x : carrier, (2 : ℤ) ∣ ((x : Fin 24 → ℤ) ⬝ᵥ (x : Fin 24 → ℤ)) / 8
  intro x
  have hdvd : (16 : ℤ) ∣ (x : Fin 24 → ℤ) ⬝ᵥ (x : Fin 24 → ℤ) := by
    rcases x.2 with hx | hx
    · obtain ⟨a, ha, hax⟩ := mem_subA2.1 hx
      obtain ⟨k, hk⟩ := four_dvd_dot_self ha.1
      exact ⟨k, by rw [← hax, dot_two_smul_two_smul, hk]; ring⟩
    · obtain ⟨a, ha, hax⟩ := mem_subA2.1 hx
      have hxa : (x : Fin 24 → ℤ) = (2 : ℤ) • a + uVec := by
        rw [hax]; ring
      obtain ⟨k, hk⟩ := four_dvd_dot_self ha.1
      obtain ⟨m, hm⟩ := ha.2
      refine ⟨k + m + a 0 + 3, ?_⟩
      have h1 : uVec ⬝ᵥ ((2 : ℤ) • a) = 2 * ((∑ i, a i) + 4 * a 0) := by
        rw [dotProduct_smul, smul_eq_mul, dotProduct_comm, dot_uVec]
      have h2 : ((2 : ℤ) • a) ⬝ᵥ uVec = 2 * ((∑ i, a i) + 4 * a 0) := by
        rw [smul_dotProduct, smul_eq_mul, dot_uVec]
      have h3 : ((2 : ℤ) • a) ⬝ᵥ ((2 : ℤ) • a) = 4 * (a ⬝ᵥ a) := dot_two_smul_two_smul a a
      rw [hxa, add_dotProduct, dotProduct_add, dotProduct_add, h1, h2, h3, uVec_dot_uVec,
        hk, hm]
      ring
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, show (16 : ℤ) * c = 8 * (2 * c) from by ring,
    Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)]
  exact ⟨c, rfl⟩

/-! ### Ranks -/

theorem finrank_subA : finrank ℤ subA = 24 := by
  refine le_antisymm ?_ ?_
  · have h := Submodule.finrank_le subA
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  · have hmem : ∀ x : Fin 24 → ℤ, (4 : ℤ) • x ∈ subA := by
      intro x
      refine ⟨?_, ?_⟩
      · have : (4 : ℤ) • x = (2 : ℤ) • ((2 : ℤ) • x) := by rw [smul_smul]; norm_num
        rw [this]
        exact two_smul_mem_preimageOfCode Code.golay _
      · refine ⟨∑ i, x i, ?_⟩
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp
    let g : (Fin 24 → ℤ) →ₗ[ℤ] subA :=
      { toFun := fun x => ⟨(4 : ℤ) • x, hmem x⟩
        map_add' := fun x y => by ext i; simp; ring
        map_smul' := fun c x => by ext i; simp; ring }
    have hg : Function.Injective g := by
      intro x y hxy
      have : (4 : ℤ) • x = (4 : ℤ) • y := congrArg Subtype.val hxy
      exact smul_right_injective _ (by norm_num) this
    have h := LinearMap.finrank_le_finrank_of_injective (f := g) hg
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

theorem finrank_carrier : finrank ℤ carrier = 24 := by
  refine le_antisymm ?_ ?_
  · have h := Submodule.finrank_le carrier
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  · have hmem : ∀ x : Fin 24 → ℤ, (8 : ℤ) • x ∈ carrier := by
      intro x
      refine Or.inl (mem_subA2.2 ⟨(4 : ℤ) • x, ?_, ?_⟩)
      · refine ⟨?_, ?_⟩
        · have : (4 : ℤ) • x = (2 : ℤ) • ((2 : ℤ) • x) := by rw [smul_smul]; norm_num
          rw [this]
          exact two_smul_mem_preimageOfCode Code.golay _
        · refine ⟨∑ i, x i, ?_⟩
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by simp
      · rw [smul_smul]; norm_num
    let g : (Fin 24 → ℤ) →ₗ[ℤ] carrier :=
      { toFun := fun x => ⟨(8 : ℤ) • x, hmem x⟩
        map_add' := fun x y => by ext i; simp; ring
        map_smul' := fun c x => by ext i; simp; ring }
    have hg : Function.Injective g := by
      intro x y hxy
      have : (8 : ℤ) • x = (8 : ℤ) • y := congrArg Subtype.val hxy
      exact smul_right_injective _ (by norm_num) this
    have h := LinearMap.finrank_le_finrank_of_injective (f := g) hg
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h

theorem lattice_rank : lattice.rank = 24 := finrank_carrier

/-! ### The two index-2 embeddings of `A` -/

theorem two_dvd_dot_subA {x : Fin 24 → ℤ} (hx : x ∈ subA) {y : Fin 24 → ℤ} (hy : y ∈ subA) :
    (2 : ℤ) ∣ x ⬝ᵥ y := two_dvd_dot hx.1 hy.1

/-- `A` as a lattice, with the same halved form as `Γ_Golay`. -/
def subALattice : IntegralLattice :=
  dotLattice 2 subA (fun _ hx _ hy => two_dvd_dot_subA hx hy)

theorem subALattice_rank : subALattice.rank = 24 := finrank_subA

/-- The inclusion `A ↪ Γ_Golay`. -/
def inclG : (↥subA) →ₗ[ℤ] (↥preG) := Submodule.inclusion subA_le_preG

theorem inclG_injective : Function.Injective inclG :=
  Submodule.inclusion_injective subA_le_preG

theorem inclG_bilin (x y : ↥subA) :
    golayLattice.bilin (inclG x) (inclG y) = subALattice.bilin x y := rfl

/-- The scaled inclusion `A ↪ Λ`, `a ↦ 2a`; doubling the vectors multiplies the dot product by
`4` while the Leech form divides by `8` instead of `2`, so this preserves the form. -/
def inclLaux : (↥subA) →ₗ[ℤ] (↥carrier) where
  toFun a := ⟨(2 : ℤ) • (a : Fin 24 → ℤ), Or.inl (two_smul_mem_subA2 a.2)⟩
  map_add' a b := by
    refine Subtype.ext (funext fun i => ?_)
    simp only [Submodule.coe_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  map_smul' c a := by
    refine Subtype.ext (funext fun i => ?_)
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The scaled inclusion `A ↪ Λ`. -/
def inclL : (↥subA) →ₗ[ℤ] (↥carrier) := inclLaux

theorem inclL_injective : Function.Injective inclL := by
  intro x y hxy
  have h : (2 : ℤ) • (x : Fin 24 → ℤ) = (2 : ℤ) • (y : Fin 24 → ℤ) :=
    congrArg Subtype.val hxy
  exact Subtype.ext (smul_right_injective _ (by norm_num) h)

theorem inclL_bilin (x y : ↥subA) :
    lattice.bilin (inclL x) (inclL y) = subALattice.bilin x y := by
  show ((2 : ℤ) • (x : Fin 24 → ℤ)) ⬝ᵥ ((2 : ℤ) • (y : Fin 24 → ℤ)) / 8
      = ((x : Fin 24 → ℤ) ⬝ᵥ (y : Fin 24 → ℤ)) / 2
  rw [dot_two_smul_two_smul]
  obtain ⟨m, hm⟩ := two_dvd_dot_subA x.2 y.2
  rw [hm, show (4 : ℤ) * (2 * m) = 8 * m from by ring,
    Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0),
    Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]

/-! ### Both embeddings have index two -/

theorem sum_add_coe (x y : ↥preG) :
    ∑ i, ((x : Fin 24 → ℤ) + (y : Fin 24 → ℤ)) i
      = (∑ i, (x : Fin 24 → ℤ) i) + ∑ i, (y : Fin 24 → ℤ) i := by
  simp only [Pi.add_apply, Finset.sum_add_distrib]

/-- Ebeling's parity homomorphism `x ↦ (∑ᵢ xᵢ)/2 mod 2` on `ρ⁻¹(Golay)`.  Its kernel is `A`. -/
def parity : (↥preG) →ₗ[ℤ] ZMod 2 where
  toFun x := ((((∑ i, (x : Fin 24 → ℤ) i) / 2 : ℤ)) : ZMod 2)
  map_add' x y := by
    simp only [Submodule.coe_add]
    rw [sum_add_coe x y, Int.add_ediv_of_dvd_left (two_dvd_sum x.2)]
    push_cast
    ring
  map_smul' c x := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [show ∑ i, (c • (x : Fin 24 → ℤ)) i = c * ∑ i, (x : Fin 24 → ℤ) i from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp,
      Int.mul_ediv_assoc _ (two_dvd_sum x.2), zsmul_eq_mul]
    push_cast
    ring

theorem parity_eq_zero_iff (x : ↥preG) :
    parity x = 0 ↔ (4 : ℤ) ∣ ∑ i, (x : Fin 24 → ℤ) i := by
  obtain ⟨m, hm⟩ := two_dvd_sum x.2
  show ((((∑ i, (x : Fin 24 → ℤ) i) / 2 : ℤ)) : ZMod 2) = 0 ↔ _
  rw [hm, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0),
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega⟩

theorem range_inclG : LinearMap.range inclG = LinearMap.ker parity := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker, parity_eq_zero_iff]
    exact a.2.2
  · intro hy
    rw [LinearMap.mem_ker, parity_eq_zero_iff] at hy
    exact ⟨⟨(y : Fin 24 → ℤ), y.2, hy⟩, rfl⟩

theorem parity_surjective : Function.Surjective parity := by
  intro z
  have hw : (2 : ℤ) • (fun i : Fin 24 => if i = 0 then (1 : ℤ) else 0) ∈ preG :=
    two_smul_mem_preimageOfCode Code.golay _
  have hval : parity ⟨_, hw⟩ = 1 := by
    show ((((∑ i, ((2 : ℤ) • (fun i : Fin 24 => if i = 0 then (1 : ℤ) else 0)) i) / 2 : ℤ))
      : ZMod 2) = 1
    rw [show (∑ i, ((2 : ℤ) • (fun i : Fin 24 => if i = 0 then (1 : ℤ) else 0)) i) = 2 from by
      decide +kernel]
    decide
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with h | h
  · exact ⟨0, by rw [h, map_zero]⟩
  · exact ⟨⟨_, hw⟩, by rw [h, hval]⟩

theorem card_quotient_inclG :
    Nat.card (golayLattice ⧸ LinearMap.range inclG) = 2 := by
  have h1 : Nat.card ((↥preG) ⧸ LinearMap.ker parity) = 2 := by
    rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective parity parity_surjective).toEquiv]
    simp
  rw [range_inclG]
  exact h1

/-- The "all coordinates have the same parity" homomorphism on the Leech carrier.  Its kernel is
`2A`. -/
def beta : (↥carrier) →ₗ[ℤ] ZMod 2 where
  toFun x := ((((x : Fin 24 → ℤ) 0 : ℤ)) : ZMod 2)
  map_add' x y := by
    simp only [Submodule.coe_add, Pi.add_apply]
    push_cast
    ring
  map_smul' c x := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, zsmul_eq_mul]
    push_cast
    ring

theorem range_inclL : LinearMap.range inclL = LinearMap.ker beta := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    show ((((2 : ℤ) • (a : Fin 24 → ℤ)) 0 : ℤ) : ZMod 2) = 0
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul]
  · intro hy
    rw [LinearMap.mem_ker] at hy
    have hy0 : (2 : ℤ) ∣ (y : Fin 24 → ℤ) 0 := by
      have h' : ((((y : Fin 24 → ℤ) 0 : ℤ)) : ZMod 2) = 0 := hy
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    rcases y.2 with h | h
    · obtain ⟨a, ha, hax⟩ := mem_subA2.1 h
      exact ⟨⟨a, ha⟩, Subtype.ext hax⟩
    · exfalso
      obtain ⟨a, ha, hax⟩ := mem_subA2.1 h
      have h0 : (y : Fin 24 → ℤ) 0 = 2 * a 0 + 5 := by
        have := congrFun hax 0
        simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this
        rw [show uVec 0 = 5 from by simp [uVec]] at this
        omega
      rw [h0] at hy0
      omega

theorem beta_surjective : Function.Surjective beta := by
  intro z
  have hu : uVec ∈ carrier := Or.inr (by simp)
  have hval : beta ⟨uVec, hu⟩ = 1 := by
    show (((uVec 0 : ℤ)) : ZMod 2) = 1
    rw [show uVec 0 = 5 from by simp [uVec]]
    decide
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with h | h
  · exact ⟨0, by rw [h, map_zero]⟩
  · exact ⟨⟨uVec, hu⟩, by rw [h, hval]⟩

theorem card_quotient_inclL :
    Nat.card (lattice ⧸ LinearMap.range inclL) = 2 := by
  have h1 : Nat.card ((↥carrier) ⧸ LinearMap.ker beta) = 2 := by
    rw [Nat.card_congr (LinearMap.quotKerEquivOfSurjective beta beta_surjective).toEquiv]
    simp
  rw [range_inclL]
  exact h1

/-! ### The determinant -/

theorem finrank_range_inclG : finrank ℤ (LinearMap.range inclG) = golayLattice.rank := by
  have h1 : finrank ℤ (LinearMap.range inclG) = finrank ℤ (↥subA) :=
    ((LinearEquiv.ofInjective inclG inclG_injective).finrank_eq).symm
  rw [h1, finrank_subA, golayLattice_rank]

theorem finrank_range_inclL : finrank ℤ (LinearMap.range inclL) = lattice.rank := by
  have h1 : finrank ℤ (LinearMap.range inclL) = finrank ℤ (↥subA) :=
    ((LinearEquiv.ofInjective inclL inclL_injective).finrank_eq).symm
  rw [h1, finrank_subA, lattice_rank]

theorem subALattice_det : subALattice.det = 4 := by
  have h := IntegralLattice.det_of_injective_index (Γ := subALattice) (Λ := golayLattice)
    inclG inclG_injective inclG_bilin finrank_range_inclG (k := 2) card_quotient_inclG
  rw [h, golayLattice_det]
  norm_num

/-- **The Leech lattice is unimodular**, by the index–determinant relation applied twice to `A`. -/
theorem lattice_det : lattice.det = 1 := by
  have h := IntegralLattice.det_of_injective_index (Γ := subALattice) (Λ := lattice)
    inclL inclL_injective inclL_bilin finrank_range_inclL (k := 2) card_quotient_inclL
  rw [subALattice_det] at h
  norm_num at h
  omega

theorem lattice_isUnimodular : lattice.IsUnimodular := by
  rw [IntegralLattice.IsUnimodular, lattice_det]
  exact isUnit_one

/-! ### The Leech lattice has no roots -/

theorem one_le_mul_self {n : ℤ} (hn : n ≠ 0) : (1 : ℤ) ≤ n * n := by
  have habs : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
  calc (1 : ℤ) = 1 * 1 := by ring
    _ ≤ |n| * |n| := by nlinarith
    _ = n * n := abs_mul_abs_self n

theorem weight_le_dot_self (a : Fin 24 → ℤ) :
    ((Code.weight (reduceMod 2 24 a) : ℕ) : ℤ) ≤ a ⬝ᵥ a := by
  rw [weight_reduceMod_eq_sum, dotProduct]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : (2 : ℤ) ∣ a i
  · simp only [h, if_true]
    exact mul_self_nonneg _
  · simp only [h, if_false]
    exact one_le_mul_self fun h0 => h (by rw [h0]; exact dvd_zero 2)

theorem two_dvd_mul_self_sub (n : ℤ) : (2 : ℤ) ∣ n * n - n := by
  rcases Int.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact ⟨2 * m * m - m, by rw [hm]; ring⟩
  · exact ⟨2 * m * m + m, by rw [hm]; ring⟩

theorem uVec_odd (i : Fin 24) : ¬ (2 : ℤ) ∣ uVec i := by
  by_cases h : i = 0
  · rw [show uVec i = 5 from by simp [uVec, h]]
    omega
  · rw [show uVec i = 1 from by simp [uVec, h]]
    omega

/-- **The Leech lattice has no roots**: no vector of norm `2`.  This is what the twist by `u` and
the parity condition `4 ∣ ∑ᵢ xᵢ` were designed for. -/
theorem lattice_normSq_ne_two : ∀ x : carrier, ((x : Fin 24 → ℤ) ⬝ᵥ (x : Fin 24 → ℤ)) / 8 ≠ 2 := by
  rintro ⟨x, hx⟩ hEq
  simp only at hEq
  obtain ⟨k, hk⟩ := eight_dvd_dot hx hx
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num : (8 : ℤ) ≠ 0)] at hEq
  have hxx : x ⬝ᵥ x = 16 := by rw [hk, hEq]; norm_num
  rcases hx with hx | hx
  · obtain ⟨a, ha, rfl⟩ := mem_subA2.1 hx
    rw [dot_two_smul_two_smul] at hxx
    have haa : a ⬝ᵥ a = 4 := by omega
    have hw := weight_le_dot_self a
    rw [haa] at hw
    have hwn : Code.weight (reduceMod 2 24 a) ≤ 4 := by exact_mod_cast hw
    have hz : reduceMod 2 24 a = 0 := by
      by_contra hne
      have h1 := Code.minDist_le_weight (mem_preG.mp ha.1) hne
      rw [Code.golay_minDist] at h1
      omega
    have heven : ∀ i, (2 : ℤ) ∣ a i := by
      intro i
      have h1 : ((a i : ℤ) : ZMod 2) = 0 := congrFun hz i
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    set b : Fin 24 → ℤ := fun i => a i / 2 with hbdef
    have hab : a = (2 : ℤ) • b := by
      funext i
      obtain ⟨c, hc⟩ := heven i
      rw [Pi.smul_apply, smul_eq_mul, hbdef]
      simp only
      rw [hc, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    have hbb : b ⬝ᵥ b = 1 := by
      have h1 : (4 : ℤ) * (b ⬝ᵥ b) = 4 := by
        rw [← dot_two_smul_two_smul, ← hab]; exact haa
      omega
    have hsuma : ∑ i, a i = 2 * ∑ i, b i := by
      rw [hab, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp
    have hpar : (2 : ℤ) ∣ (b ⬝ᵥ b) - ∑ i, b i := by
      rw [dotProduct, ← Finset.sum_sub_distrib]
      exact Finset.dvd_sum fun i _ => two_dvd_mul_self_sub (b i)
    rw [hbb] at hpar
    obtain ⟨m, hm⟩ := ha.2
    rw [hsuma] at hm
    omega
  · obtain ⟨a, ha, hax⟩ := mem_subA2.1 hx
    have hcoord : ∀ i, x i = 2 * a i + uVec i := by
      intro i
      have h1 := congrFun hax i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1
      omega
    have hodd : ∀ i, x i ≠ 0 := by
      intro i h0
      refine uVec_odd i ⟨-(a i), ?_⟩
      have := hcoord i
      omega
    have hge : (24 : ℤ) ≤ x ⬝ᵥ x := by
      rw [dotProduct]
      calc (24 : ℤ) = ∑ _i : Fin 24, (1 : ℤ) := by simp
        _ ≤ ∑ i, x i * x i := Finset.sum_le_sum fun i _ => one_le_mul_self (hodd i)
    omega

theorem lattice_no_roots (x : lattice) : normSq x ≠ 2 := lattice_normSq_ne_two x

end Leech
