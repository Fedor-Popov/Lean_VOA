import VOA.Classification.COne.OrbOctaSpan
import VOA.Classification.COne.V2Icosahedral

/-! # OrbIco: the standard icosahedral subgroup `ico ≤ Aut V₂` and its action on polynomials

`ico := icoHom.range` (`V2Icosahedral.lean`), the rotation group of the dodecahedron whose cube
vertices are `(±1, ±1, ±1)`. It contains the coordinate half-turns and the cyclic permutation
`rotC`, so it contains the standard tetrahedral group.

* `ico_eq_closure`: `ico = ⟨rotC, rotR⟩` (`sigC`, `sigR` generate `A₅`).
* `autL_rotC`, `autL_rotR`: the matrices on `(V₂)₁`.
* `ico_lift`: every `g ∈ ico` acts on binary forms compatibly with `psi`
  (`psi ∘ φ_g = β_g ∘ psi` for an algebra endomorphism `β_g` of `ℂ[x,y]`), from the explicit
  lifts `betaC`, `betaR` of the generators (spin lifts, `SL₂ → SO₃`).
* `IcoInv`, the Reynolds operator `reyI`, and `psi_reyI`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv OrbPrim OrbOcta
  Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## `A₅ = ⟨sigC, sigR⟩` -/

theorem closure_sigC_sigR :
    Subgroup.closure ({⟨sigC, sigC_alt⟩, ⟨sigR, sigR_alt⟩} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  set K := Subgroup.closure ({⟨sigC, sigC_alt⟩, ⟨sigR, sigR_alt⟩} : Set (alternatingGroup (Fin 5)))
  have hC : (⟨sigC, sigC_alt⟩ : alternatingGroup (Fin 5)) ∈ K :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hR : (⟨sigR, sigR_alt⟩ : alternatingGroup (Fin 5)) ∈ K :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hdvd : ∀ (g : alternatingGroup (Fin 5)) (p : ℕ) [Fact p.Prime], g ∈ K →
      g ^ p = 1 → g ≠ 1 → p ∣ Nat.card K := by
    intro g p _ hg hp h1
    rw [← orderOf_eq_prime hp h1]
    exact K.orderOf_dvd_natCard hg
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h2 := hdvd _ 2 hR (by decide) (by decide)
  have h3 := hdvd _ 3 hC (by decide) (by decide)
  have h5 := hdvd _ 5 (K.mul_mem hC hR) (by decide) (by decide)
  have hK := K.card_subgroup_dvd_card
  rw [nat_card_A5] at hK
  have hle := Nat.le_of_dvd (by norm_num) hK
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hcases : Nat.card K = 30 ∨ Nat.card K = 60 := by omega
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

/-! ## The subgroup `ico` -/

/-- The standard icosahedral subgroup of `Aut V₂`. -/
def ico : Subgroup (Aut V1) := icoHom.range

theorem icoHom_sigC : icoHom ⟨sigC, sigC_alt⟩ = rotC :=
  (icoFun_spec ⟨sigC, sigC_alt⟩).unique isIco_rotC

theorem icoHom_sigR : icoHom ⟨sigR, sigR_alt⟩ = rotR :=
  (icoFun_spec ⟨sigR, sigR_alt⟩).unique isIco_rotR

theorem rotC_mem : rotC ∈ ico := ⟨_, icoHom_sigC⟩
theorem rotR_mem : rotR ∈ ico := ⟨_, icoHom_sigR⟩

theorem ico_eq_closure : ico = Subgroup.closure {rotC, rotR} := by
  rw [ico, MonoidHom.range_eq_map, ← closure_sigC_sigR, MonoidHom.map_closure, Set.image_pair,
    icoHom_sigC, icoHom_sigR]

/-- Induction over `ico` from the two generators. -/
theorem ico_induction {p : Aut V1 → Prop} (h1 : p 1) (hmul : ∀ x y, p x → p y → p (x * y))
    (hC : p rotC) (hCi : p rotC⁻¹) (hR : p rotR) (hRi : p rotR⁻¹) :
    ∀ g ∈ ico, p g := by
  intro g hg
  rw [ico_eq_closure] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hC
    · exact hR
  | inv_mem x hx =>
    rcases hx with rfl | rfl
    · exact hCi
    · exact hRi
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem ico_finite : Finite ico :=
  Finite.of_equiv (alternatingGroup (Fin 5)) (MonoidHom.ofInjective icoHom_injective).toEquiv

noncomputable instance icoFintype : Fintype ico := @Fintype.ofFinite _ ico_finite

/-! ## The generators on `(V₂)₁` -/

theorem autL_rotC (v : Fin 3 → ℂ) : autL rotC v = ![v 1, v 2, v 0] := by
  apply xyzL_injective
  rw [xyzL_autL]
  simp only [xyzL_apply, rotC_xyz]
  simp

theorem autL_rotR (v : Fin 3 → ℂ) : autL rotR v =
    ![(gq * v 0 + gp * v 1 + v 2) / 2, (gp * v 0 - v 1 + gq * v 2) / 2,
      (v 0 + gq * v 1 - gp * v 2) / 2] := by
  apply xyzL_injective
  rw [xyzL_autL]
  simp only [xyzL_apply, rotR_xyz]
  simp

theorem phiE_lin (g : Aut V1) (v : Fin 3 → ℂ) : phiE g (lin v) = lin (autL g v) := by
  rw [phiE_apply, substL_lin]

theorem phiE_X (g : Aut V1) (k : Fin 3) : phiE g (X k) = lin (autL g (Pi.single k 1)) := by
  rw [← lin_single, phiE_lin]

theorem lin_apply (v : Fin 3 → ℂ) :
    lin v = MvPolynomial.C (v 0) * X 0 + MvPolynomial.C (v 1) * X 1 + MvPolynomial.C (v 2) * X 2 := by
  change ∑ k, v k • (X k : P3) = _
  rw [Fin.sum_univ_three, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]

theorem phiE_inv_of_fix {g : Aut V1} {F : P3} (h : phiE g F = F) : phiE g⁻¹ F = F := by
  have := congrArg (phiE g⁻¹) h
  rw [← phiE_mul, inv_mul_cancel] at this
  rw [← this]
  change phiHom 1 F = F
  rw [map_one]
  rfl

/-! ## Invariants and the Reynolds operator -/

/-- `ico`-invariance of a polynomial. -/
def IcoInv (F : P3) : Prop := ∀ g ∈ ico, phiE g F = F

theorem icoInv_of_gen {F : P3} (hC : phiE rotC F = F) (hR : phiE rotR F = F) : IcoInv F :=
  ico_induction (p := fun g => phiE g F = F) (by change phiHom 1 F = F; rw [map_one]; rfl)
    (fun x y hx hy => by simp only at hx hy ⊢; rw [phiE_mul, hy, hx]) hC (phiE_inv_of_fix hC) hR (phiE_inv_of_fix hR)

theorem IcoInv.mul {F G : P3} (hF : IcoInv F) (hG : IcoInv G) : IcoInv (F * G) :=
  fun g hg => by rw [map_mul, hF g hg, hG g hg]

theorem IcoInv.pow {F : P3} (hF : IcoInv F) (n : ℕ) : IcoInv (F ^ n) :=
  fun g hg => by rw [map_pow, hF g hg]

theorem IcoInv.sub {F G : P3} (hF : IcoInv F) (hG : IcoInv G) : IcoInv (F - G) :=
  fun g hg => by rw [map_sub, hF g hg, hG g hg]

theorem IcoInv.smul {F : P3} (hF : IcoInv F) (c : ℂ) : IcoInv (c • F) :=
  fun g hg => by rw [map_smul, hF g hg]

theorem icoInv_one : IcoInv 1 := fun _ _ => map_one _

/-- The Reynolds operator of `ico` on `ℂ[x,y,z]`. -/
def reyI (F : P3) : P3 := ((Fintype.card ico : ℂ)⁻¹) • ∑ g : ico, phiE g.1 F

theorem card_ico_ne_zero : (Fintype.card ico : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem reyI_fix (F : P3) {h : Aut V1} (hh : h ∈ ico) : phiE h (reyI F) = reyI F := by
  unfold reyI
  rw [map_smul, map_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulLeft (⟨h, hh⟩ : ico)) (fun g : ico => phiE g.1 F)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Equiv.coe_mulLeft, Subgroup.coe_mul, phiE_mul]

theorem icoInv_reyI (F : P3) : IcoInv (reyI F) := fun _ hg => reyI_fix F hg

theorem reyI_of_inv {F : P3} (hF : IcoInv F) : reyI F = F := by
  unfold reyI
  rw [Finset.sum_congr rfl (fun g _ => hF g.1 g.2), Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ card_ico_ne_zero, one_smul]

theorem reyI_hom {F : P3} {n : ℕ} (hF : F.IsHomogeneous n) : (reyI F).IsHomogeneous n := by
  rw [← mem_homogeneousSubmodule]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ =>
    (mem_homogeneousSubmodule _ _).mpr (by rw [phiE_apply]; exact substL_hom _ hF))

/-- If every `g ∈ ico` sends `F` to a polynomial with the same binary image `B`, so does the
Reynolds average. -/
theorem psi_reyI {F : P3} {B : P2} (h : ∀ g ∈ ico, psi (phiE g F) = B) : psi (reyI F) = B := by
  unfold reyI
  rw [map_smul, map_sum, Finset.sum_congr rfl (fun g _ => h g.1 g.2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ card_ico_ne_zero,
    one_smul]

end VOA.Classification.COne.OrbIco
