/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.V2Automorphisms
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The icosahedral group `A₅ ≤ Aut V₂`

Completes `V2Automorphisms.lean` by realizing the last exceptional clause of `InCOneList`.

## Method
On `(V₂)₁ ≅ sl₂` with the coordinates `xyz a b c` of `V2Automorphisms.lean` (where the invariant
form is `a² + b² + c²`), three automorphisms act by explicit rotations:
* `rotC = rot2 * rot4 : (a,b,c) ↦ (b,c,a)` and `rotZ = rot4 * rot4 : (a,b,c) ↦ (−a,−b,c)`;
* `rotR = exp(p E) g_u exp(ε q F)` with `p = −3/2 − (√5 + √5 i + i)/2`, `q = (1−i)(−√5−2−i)/2`,
  `u = −6 − 2√5`: the half-turn about `(φ, 1, φ⁻¹)` (`rotR_xyz`), with `φ = (1+√5)/2` (`gp`).

The twenty dodecahedral vertices are labelled by ordered pairs `(j,k)` of distinct elements of
`Fin 5` (`v ∈ T_j`, `−v ∈ T_k` for the five inscribed tetrahedra `T_j` of one chirality), giving
vectors `dv j k`. `IsIco σ φ` says `φ (dv j k) = dv (σ j) (σ k)`; it is multiplicative, and unique
in `φ` by rigidity (`aut_ext_of_agree`), since `h` and `e^α` are combinations of the `dv j k`.
`rotC`, `rotZ`, `rotR` realize `(1 2 3)`, `(1 4)(2 3)`, `(0 3)(2 4)` (`isIco_rot*`, by direct
computation in `ℚ(√5, i)`). The realized even permutations form a subgroup of `A₅` containing
elements of orders `2, 3, 5`, hence of order `30` or `60`; order `30` would make it normal (index
two), contradicting simplicity of `A₅` (`alternatingGroup.isSimpleGroup_five`). So every element of
`A₅` is realized, giving `icoHom : A₅ →* Aut V₂`, injective again by simplicity (`sigR` acts
nontrivially).

## Main results
* `exists_A5_subgroup : ∃ G ≤ Aut V₂, G ≃* A₅`.
* `exists_hasCOneLabel_icosa`: the clause `IsV2Orbifold _ (alternatingGroup (Fin 5))` is
  realized by `V₂^G`.

## Status
`sorry`-free, no new axioms. Unconditional. (`rotZ` / `isIco_rotZ` are recorded for completeness;
the generation argument only uses `rotC` and `rotR`.)
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN Complex Equiv

section Icosahedral

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- `√5 ∈ ℂ`. -/
noncomputable def s5 : ℂ := ((Real.sqrt 5 : ℝ) : ℂ)

theorem s5_sq : s5 ^ 2 = 5 := by
  rw [s5, ← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem s5_pow_three : s5 ^ 3 = 5 * s5 := by rw [pow_succ, s5_sq]

theorem s5_pow_four : s5 ^ 4 = 25 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, s5_sq]; norm_num

/-- The golden ratio `φ = (1 + √5)/2` and `φ⁻¹ = (√5 − 1)/2`, in `ℂ`. -/
noncomputable def gp : ℂ := (1 + s5) / 2
noncomputable def gq : ℂ := (s5 - 1) / 2

theorem unitG_mul : (-6 - 2 * s5) * ((s5 - 3) / 8) = 1 := by
  linear_combination (-1 / 4 : ℂ) * s5_sq

theorem unitG_inv : (-6 - 2 * s5)⁻¹ = (s5 - 3) / 8 := inv_eq_of_mul_eq_one_right unitG_mul

/-- The unit `−6 − 2√5 = −4φ²`. -/
noncomputable def unitG : ℂˣ := Units.mk0 (-6 - 2 * s5) (left_ne_zero_of_mul_eq_one unitG_mul)

theorem I_pow_five : I ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
theorem I_pow_six : I ^ 6 = -1 := by rw [pow_succ, I_pow_five, I_mul_I]
theorem I_pow_seven : I ^ 7 = -I := by rw [pow_succ, I_pow_six, neg_one_mul]
theorem s5_pow_five : s5 ^ 5 = 25 * s5 := by rw [pow_succ, s5_pow_four]

/-- The parameters of the icosahedral half-turn. -/
noncomputable def pR : ℂ := -3 / 2 - (s5 + s5 * I + I) / 2
noncomputable def qR : ℂ := (1 - I) * (-s5 - 2 - I) / 2

/-- The rotation by `π` about the axis `(φ, 1, φ⁻¹)`: `exp(p E) g_u exp(ε q F)`. -/
noncomputable def rotR : Aut V1 := expE pR * charU 1 le_rfl unitG * expF (eps1 * qR)

theorem rotR_xyz (a b c : ℂ) :
    rotR (xyz a b c) = xyz ((gq * a + gp * b + c) / 2) ((gp * a - b + gq * c) / 2)
      ((a + gq * b - gp * c) / 2) := by
  simp only [rotR, Aut.mul_apply, xyz]
  rw [rootExp_vec3_neg _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root latP1_root', charU_vec3,
    rootExp_vec3_pos _ (latP_posDef 1 le_rfl) (latP_even 1) latP1_root]
  simp only [cocycle_eq_eps1, unitG, Units.val_mk0, unitG_inv, pR, qR, gp, gq]
  rcases eps1_cases with h | h <;> rw [h] <;> apply vec3_congr <;>
    (ring_nf; simp only [I_sq, I_pow_three, I_pow_four, I_pow_five, I_pow_six, I_pow_seven, s5_sq, s5_pow_three,
      s5_pow_four, s5_pow_five]; ring_nf)

/-- `rot2 * rot4 : (a,b,c) ↦ (b,c,a)`, the 3-fold rotation about `(1,1,1)`. -/
noncomputable def rotC : Aut V1 := rot2 * rot4

theorem rotC_xyz (a b c : ℂ) : rotC (xyz a b c) = xyz b c a := by
  rw [rotC, Aut.mul_apply, rot4_xyz, rot2_xyz, neg_neg]

/-- `rot4 * rot4 : (a,b,c) ↦ (−a,−b,c)`, the half-turn about `Z`. -/
noncomputable def rotZ : Aut V1 := rot4 * rot4

theorem rotZ_xyz (a b c : ℂ) : rotZ (xyz a b c) = xyz (-a) (-b) c := by
  rw [rotZ, Aut.mul_apply, rot4_xyz, rot4_xyz]

/-! ### The dodecahedron

The twenty vertices `(±1,±1,±1)`, `(0,±φ,±φ⁻¹)`, `(±φ,±φ⁻¹,0)`, `(±φ⁻¹,0,±φ)` are labelled by the
ordered pairs `(j,k)`, `j ≠ k`, of `Fin 5`: the vertex `v` gets `(j,k)` when `v` lies in the `j`-th
and `−v` in the `k`-th of the five inscribed tetrahedra of one chirality (`dv k j = −dv j k`,
`dv j j = 0`). The rotation group acts on the tetrahedra through `A₅`, and on the vertices by
`v_{jk} ↦ v_{σj,σk}`. -/

noncomputable def da : Fin 5 → Fin 5 → ℂ :=
  ![![0, -1, -1, 1, 1], ![1, 0, 0, gq, -gp], ![1, 0, 0, -gp, gq], ![-1, -gq, gp, 0, 0], ![-1, gp, -gq, 0, 0]]
noncomputable def db : Fin 5 → Fin 5 → ℂ :=
  ![![0, -1, 1, -1, 1], ![1, 0, -gp, 0, gq], ![-1, gp, 0, -gq, 0], ![1, 0, gq, 0, -gp], ![-1, -gq, 0, gp, 0]]
noncomputable def dc : Fin 5 → Fin 5 → ℂ :=
  ![![0, 1, -1, -1, 1], ![-1, 0, -gq, gp, 0], ![1, gq, 0, 0, -gp], ![1, -gp, 0, 0, gq], ![-1, 0, gp, -gq, 0]]

/-- The dodecahedral vectors in `(V₂)₁ ≅ sl₂`. -/
noncomputable def dv (j k : Fin 5) : LatModuleGen (latP 1) := xyz (da j k) (db j k) (dc j k)

/-- `φ` realizes the permutation `σ` of the five tetrahedra: `φ(v_{jk}) = v_{σj,σk}`. -/
def IsIco (σ : Perm (Fin 5)) (φ : Aut V1) : Prop := ∀ j k, φ (dv j k) = dv (σ j) (σ k)

theorem IsIco.mul {σ τ : Perm (Fin 5)} {φ ψ : Aut V1} (h1 : IsIco σ φ) (h2 : IsIco τ ψ) :
    IsIco (σ * τ) (φ * ψ) := by
  intro j k
  rw [Aut.mul_apply, h2, h1]; rfl

theorem IsIco.one : IsIco 1 (1 : Aut V1) := fun _ _ => rfl

theorem IsIco.inv {σ : Perm (Fin 5)} {φ : Aut V1} (h : IsIco σ φ) : IsIco σ⁻¹ φ⁻¹ := by
  intro j k
  have h1 := h (σ⁻¹ j) (σ⁻¹ k)
  rw [show σ (σ⁻¹ j) = j from σ.apply_symm_apply j, show σ (σ⁻¹ k) = k from σ.apply_symm_apply k]
    at h1
  rw [← h1]
  exact φ.toLinearEquiv.symm_apply_apply _

theorem hSt_eq_dv : hSt (latP 1) (a1 1) = (1 / 2 : ℂ) • (dv 0 4 + dv 0 1) := by
  rw [hSt_eq_xyz, dv, dv, xyz_add, xyz_smul]
  apply xyz_congr <;> simp [da, db, dc]
  norm_num

theorem latChargeGen_eq_dv : latChargeGen (latP 1) (a1 1)
    = (1 / 4 : ℂ) • (dv 0 4 + dv 0 3) + (-I / 4) • (dv 0 4 + dv 0 2) := by
  rw [latChargeGen_eq_xyz, dv, dv, dv, xyz_add, xyz_add, xyz_smul, xyz_smul, xyz_add]
  apply xyz_congr <;> simp [da, db, dc] <;> ring

theorem IsIco.unique {σ : Perm (Fin 5)} {φ ψ : Aut V1} (h1 : IsIco σ φ) (h2 : IsIco σ ψ) :
    φ = ψ := by
  have h : ∀ j k, φ (dv j k) = ψ (dv j k) := fun j k => by rw [h1, h2]
  apply aut_ext_of_agree 1 le_rfl
  · simp only [hSt_eq_dv, map_add, Aut.map_smul_c, h]
  · simp only [latChargeGen_eq_dv, map_add, Aut.map_smul_c, h]

/-- The permutations of the five tetrahedra induced by `rotC`, `rotZ`, `rotR`. -/
def sigC : Perm (Fin 5) := swap 1 2 * swap 2 3
def sigZ : Perm (Fin 5) := swap 1 4 * swap 2 3
def sigR : Perm (Fin 5) := swap 0 3 * swap 2 4

theorem isIco_rotC : IsIco sigC rotC := by
  intro j k
  rw [dv, rotC_xyz, dv]
  fin_cases j <;> fin_cases k <;> apply xyz_congr <;> simp [da, db, dc, sigC, swap_apply_def]

theorem isIco_rotZ : IsIco sigZ rotZ := by
  intro j k
  rw [dv, rotZ_xyz, dv]
  fin_cases j <;> fin_cases k <;> apply xyz_congr <;> simp [da, db, dc, sigZ, swap_apply_def]

theorem isIco_rotR : IsIco sigR rotR := by
  intro j k
  rw [dv, rotR_xyz, dv]
  fin_cases j <;> fin_cases k <;> apply xyz_congr <;> simp [da, db, dc, sigR, swap_apply_def] <;>
    (simp only [gp, gq]; ring_nf) <;> (simp only [s5_sq]; ring_nf)

/-! ### Every even permutation of the five tetrahedra is realized -/

/-- The permutations of the five tetrahedra realized by automorphisms of `V₂`. -/
def icoSub : Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∃ φ : Aut V1, IsIco σ φ}
  mul_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ * ψ, hφ.mul hψ⟩
  one_mem' := ⟨1, IsIco.one⟩
  inv_mem' := fun ⟨φ, hφ⟩ => ⟨φ⁻¹, hφ.inv⟩

theorem sigC_mem : sigC ∈ icoSub := ⟨rotC, isIco_rotC⟩
theorem sigR_mem : sigR ∈ icoSub := ⟨rotR, isIco_rotR⟩

theorem sigC_alt : sigC ∈ alternatingGroup (Fin 5) := by
  simp [Perm.mem_alternatingGroup, sigC, Perm.sign_mul]
theorem sigR_alt : sigR ∈ alternatingGroup (Fin 5) := by
  simp [Perm.mem_alternatingGroup, sigR, Perm.sign_mul]

theorem nat_card_A5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl

/-- **`A₅ ≤ ` the realized permutations.** The subgroup `K = icoSub ∩ A₅` contains elements of
orders `2` (`sigR`), `3` (`sigC`) and `5` (`sigC * sigR`), so `30 ∣ |K|`; an index-two subgroup
would be normal, contradicting the simplicity of `A₅`. -/
theorem alternatingGroup_le_icoSub : alternatingGroup (Fin 5) ≤ icoSub := by
  set K := icoSub.subgroupOf (alternatingGroup (Fin 5))
  have hdvd : ∀ (g : alternatingGroup (Fin 5)) (p : ℕ) [Fact p.Prime], (g : Perm (Fin 5)) ∈ icoSub →
      (g : Perm (Fin 5)) ^ p = 1 → (g : Perm (Fin 5)) ≠ 1 → p ∣ Nat.card K := by
    intro g p _ hg hp h1
    have hord : orderOf g = p :=
      orderOf_eq_prime (Subtype.ext (by simpa using hp)) (fun h => h1 (by simp [h]))
    rw [← hord]
    exact K.orderOf_dvd_natCard (Subgroup.mem_subgroupOf.mpr hg)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2 := hdvd ⟨sigR, sigR_alt⟩ 2 sigR_mem (by decide) (by decide)
  have h3 := hdvd ⟨sigC, sigC_alt⟩ 3 sigC_mem (by decide) (by decide)
  have h5 := hdvd ⟨sigC * sigR, mul_mem sigC_alt sigR_alt⟩ 5 (mul_mem sigC_mem sigR_mem)
    (by decide) (by decide)
  have hK := K.card_subgroup_dvd_card
  rw [nat_card_A5] at hK
  have hle := Nat.le_of_dvd (by norm_num) hK
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hcases : Nat.card K = 30 ∨ Nat.card K = 60 := by omega
  have htop : K = ⊤ := by
    rcases hcases with h | h
    · have hi : K.index = 2 := by
        have := K.index_mul_card
        rw [h, nat_card_A5] at this
        omega
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K (Subgroup.normal_of_index_eq_two hi)
        with hb | ht
      · rw [hb, Subgroup.card_bot] at h
        omega
      · exact ht
    · exact Subgroup.eq_top_of_card_eq K (h.trans nat_card_A5.symm)
  intro σ hσ
  have : (⟨σ, hσ⟩ : alternatingGroup (Fin 5)) ∈ K := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_isIco (σ : alternatingGroup (Fin 5)) : ∃ φ : Aut V1, IsIco σ φ :=
  alternatingGroup_le_icoSub σ.2

/-- The automorphism realizing the even permutation `σ`. -/
noncomputable def icoFun (σ : alternatingGroup (Fin 5)) : Aut V1 := (exists_isIco σ).choose

theorem icoFun_spec (σ : alternatingGroup (Fin 5)) : IsIco σ (icoFun σ) :=
  (exists_isIco σ).choose_spec

/-- **`A₅ → Aut V₂`**, the icosahedral rotation group acting on `(V₂)₁ ≅ sl₂`. -/
noncomputable def icoHom : alternatingGroup (Fin 5) →* Aut V1 where
  toFun := icoFun
  map_one' := (icoFun_spec 1).unique IsIco.one
  map_mul' σ τ := (icoFun_spec (σ * τ)).unique ((icoFun_spec σ).mul (icoFun_spec τ))

theorem s5_ne_neg_three : s5 ≠ -3 := by
  intro h
  have := congrArg Complex.re h
  simp only [s5, ofReal_re, neg_re] at this
  have h3 : (3 : ℂ).re = 3 := by norm_num
  rw [h3] at this
  linarith [Real.sqrt_nonneg 5]

/-- `icoHom` is injective: its kernel is normal in the simple group `A₅`, and `sigR` acts
nontrivially (it moves `v_{01} = (−1,−1,1)` to `v_{31} = (−φ⁻¹, 0, −φ)`). -/
theorem icoHom_injective : Function.Injective icoHom := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ icoHom.normal_ker with h | h
  · exact h
  · exfalso
    have hm : (⟨sigR, sigR_alt⟩ : alternatingGroup (Fin 5)) ∈ icoHom.ker := h ▸ Subgroup.mem_top _
    have hs := icoFun_spec ⟨sigR, sigR_alt⟩ 0 1
    change icoHom _ (dv 0 1) = _ at hs
    rw [MonoidHom.mem_ker.mp hm] at hs
    change dv 0 1 = dv (sigR 0) (sigR 1) at hs
    rw [show sigR 0 = 3 by decide, show sigR 1 = 1 by decide, dv, dv, xyz, xyz] at hs
    have h1 := vec3_coord_two hs
    simp only [dc] at h1
    have h2 : (1 : ℂ) = -gp := by simpa using h1
    exact s5_ne_neg_three (by rw [gp] at h2; linear_combination 2 * h2)

end Icosahedral

/-- **`A₅ ≤ Aut V₂`** (the icosahedral group). -/
theorem exists_A5_subgroup :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 5)) :=
  ⟨icoHom.range, ⟨(MonoidHom.ofInjective icoHom_injective).symm⟩⟩

/-- Some fixed-point algebra `V₂^G` carries the label `icosa` (`G ≅ A₅`). -/
theorem exists_hasCOneLabel_icosa :
    ∃ G : Subgroup (Aut (V2m 1 le_rfl)), HasCOneLabel (orbifoldVOA G) .icosa := by
  obtain ⟨G, ⟨e⟩⟩ := exists_A5_subgroup
  exact ⟨G, G, ⟨e⟩, voaIsomorphic_refl' _⟩

end VOA.Classification.COne
