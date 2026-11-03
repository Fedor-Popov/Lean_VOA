import VOA.Classification.COne.OrbRat5Four

/-! # Lifting automorphisms of `V₂` to the `V₂`-module `V_{A₁+α/2}`

The module `Mo = latticeModule 1 _ 1` (the spin-½ module `V_{ℤβ+β/2}` of `V₂ = V_{ℤβ}`,
`⟨β,β⟩ = 2`) is built by transport through the gluing lattice `N = glueLat 1 1`:
`Ψ : V_{ℤβ} → V_N` with `Ψ Y_M(u,z) = Y_N(Φ u,z) Ψ`.  Hence every automorphism `G` of the
lattice VOA `V_N` which preserves `im Ψ` and satisfies `G ∘ Φ = Φ ∘ α` (`α ∈ Aut V₂`) induces a
linear operator `lift G = Ψ⁻¹ G Ψ` on the module with

  `lift G (u₍ₙ₎ x) = (α u)₍ₙ₎ (lift G x)`                (`lift_mode`).

We construct such `G` for the root exponentials `exp(c e₀)`, `exp(c f₀)` and for the torus
`charU u`, hence (`GR`) for the cubic rotation `rotC = rot2 * rot4`; `lift GR` commutes with the
modes of every `rotC`-fixed vector.  The root exponentials act on the module as the finite
exponential series of the module zero modes `D± = (e^{±β})₍₀₎` (`lift_GE`, `lift_GF`), and the
torus acts by `u^n` on the charge-`n` sector (`lift_GC`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat6

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod Complex

/-! ## §1 Notation -/

/-- `V₂ = V_{ℤβ}`. -/
abbrev V1 := latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)
/-- The gluing lattice VOA `V_N`. -/
abbrev VN := latticeVOAGen (glueLat 1 1) (glueLat_even 1 1) (glueLat_posDef 1 le_rfl 1)

/-- The module carrier. -/
abbrev Sp := LatModuleGen (latP 1)

/-- The shifted embedding `Ψ`. -/
abbrev Psi : Sp →ₗ[ℂ] LatModuleGen (glueLat 1 1) :=
  shiftEmb (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1)
/-- Its left inverse. -/
abbrev PsiInv : LatModuleGen (glueLat 1 1) →ₗ[ℂ] Sp :=
  shiftEmbInv (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1)
/-- The lattice morphism `Φ : V₂ → V_N`. -/
abbrev Phi : Sp →ₗ[ℂ] LatModuleGen (glueLat 1 1) :=
  latMorph (latP 1) (glueLat 1 1) (glueIota 1 1)

/-- The module `V_{ℤβ+β/2}`. -/
abbrev Mo : OrdVModule (V2m 1 le_rfl) Sp := latticeModule 1 le_rfl 1

theorem PsiInv_Psi (x : Sp) : PsiInv (Psi x) = x :=
  shiftEmbInv_shiftEmb (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1)
    (latP_posDef 1 le_rfl) (glueLat_posDef 1 le_rfl 1) (glueIota_isometry 1 1) x

theorem Psi_inj : Function.Injective Psi :=
  shiftEmb_injective (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1)
    (latP_posDef 1 le_rfl) (glueLat_posDef 1 le_rfl 1) (glueIota_isometry 1 1)

theorem Phi_hom : IsVOAHom V1 VN Phi :=
  latMorph_isVOAHom (latP 1) (glueLat 1 1) (glueIota 1 1) (latP_posDef 1 le_rfl)
    (glueLat_posDef 1 le_rfl 1) (glueIota_isometry 1 1) (latP_even 1) (glueLat_even 1 1)

/-- The defining intertwining of the module. -/
theorem Psi_mode (u : Sp) (n : ℤ) (x : Sp) :
    Psi (mode (Mo.YM u) n x) = VN.smul (Phi u) n (Psi x) :=
  shiftWeakModule_intertw (latP 1) (glueLat 1 1) (glueIota 1 1) (glueDelta 1 1) (latP_even 1)
    (latP_posDef 1 le_rfl) (glueLat_even 1 1) (glueLat_posDef 1 le_rfl 1)
    (glueIota_isometry 1 1) u (-n - 1) x

/-! ## §2 The lift of an automorphism of `V_N` -/

/-- `lift G = Ψ⁻¹ ∘ G ∘ Ψ`. -/
def lift (G : Aut VN) : Sp →ₗ[ℂ] Sp :=
  PsiInv ∘ₗ G.toLinearEquiv.toLinearMap ∘ₗ Psi

/-- `G` preserves the image of `Ψ`. -/
def PresR (G : Aut VN) : Prop := ∀ x : Sp, ∃ y : Sp, Psi y = G (Psi x)

theorem Psi_lift {G : Aut VN} (hR : PresR G) (x : Sp) : Psi (lift G x) = G (Psi x) := by
  obtain ⟨y, hy⟩ := hR x
  change Psi (PsiInv (G (Psi x))) = _
  rw [← hy, PsiInv_Psi]

/-- The lift intertwines `Y_M(u)` with `Y_M(α u)`. -/
theorem lift_mode {G : Aut VN} {α : Aut V1} (hR : PresR G)
    (hΦ : ∀ u, G (Phi u) = Phi (α u)) (u : Sp) (n : ℤ) (x : Sp) :
    lift G (mode (Mo.YM u) n x) = mode (Mo.YM (α u)) n (lift G x) := by
  apply Psi_inj
  rw [Psi_lift hR, Psi_mode, Aut.map_smul, hΦ, Psi_mode, Psi_lift hR]

theorem presR_mul {G₁ G₂ : Aut VN} (h₁ : PresR G₁) (h₂ : PresR G₂) : PresR (G₁ * G₂) := by
  intro x
  obtain ⟨y, hy⟩ := h₂ x
  obtain ⟨z, hz⟩ := h₁ y
  exact ⟨z, by rw [hz, hy]; rfl⟩

theorem lift_mul {G₁ G₂ : Aut VN} (h₂ : PresR G₂) (x : Sp) :
    lift (G₁ * G₂) x = lift G₁ (lift G₂ x) := by
  change PsiInv ((G₁ * G₂) (Psi x)) = PsiInv (G₁ (Psi (lift G₂ x)))
  rw [Psi_lift h₂]
  rfl

/-! ## §3 Exponentials of commuting locally nilpotent operators -/

section ExpMap

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem pow_map_comm (f : V →ₗ[ℂ] W) {D : Module.End ℂ V} {D' : Module.End ℂ W}
    (h : ∀ v, f (D v) = D' (f v)) (k : ℕ) (v : V) : f ((D ^ k) v) = (D' ^ k) (f v) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]

theorem expSum_map (f : V →ₗ[ℂ] W) {D : Module.End ℂ V} {D' : Module.End ℂ W}
    (h : ∀ v, f (D v) = D' (f v)) (N : ℕ) (v : V) : f (expSum D N v) = expSum D' N (f v) := by
  unfold expSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, pow_map_comm f h]

theorem expFun_map (f : V →ₗ[ℂ] W) {D : Module.End ℂ V} {D' : Module.End ℂ W}
    (hD : IsLocNilp D) (hD' : IsLocNilp D') (h : ∀ v, f (D v) = D' (f v)) (v : V) :
    f (expFun hD v) = expFun hD' (f v) := by
  obtain ⟨N, hN⟩ := hD v
  have hN' : (D' ^ N) (f v) = 0 := by rw [← pow_map_comm f h, hN, map_zero]
  rw [expFun_eq_expSum hD hN, expFun_eq_expSum hD' hN', expSum_map f h]

end ExpMap

/-! ## §4 Root exponentials -/

theorem root_pos : (glueLat 1 1).form (glueIota 1 1 (a1 1)) (glueIota 1 1 (a1 1)) = 2 := by
  rw [glueIota_isometry]; exact latP1_root

theorem root_neg : (glueLat 1 1).form (glueIota 1 1 (-a1 1)) (glueIota 1 1 (-a1 1)) = 2 := by
  rw [glueIota_isometry]; exact latP1_root'

/-- The module zero mode of `e^{±β}`. -/
abbrev Dpm (k : (latP 1).carrier) : Module.End ℂ Sp := mode (Mo.YM (latChargeGen (latP 1) k)) 0

/-- `Φ(c e^γ) = c c(γ) e^{ιγ}`. -/
theorem Phi_charge (c : ℂ) (γ : (latP 1).carrier) :
    Phi (c • latChargeGen (latP 1) γ) =
      (c * latCob (latP 1) (glueLat 1 1) (glueIota 1 1) γ) • latChargeGen (glueLat 1 1)
        (glueIota 1 1 γ) := by
  rw [map_smul]
  change c • latMorphC _ _ _ _ (latChargeGen (latP 1) γ) = _
  rw [latMorphC_latChargeGen, smul_smul]

/-- The `V_N` root exponential lifting `exp(c (e^γ)₍₀₎)`, `γ = ±β`. -/
def GX {γ : (latP 1).carrier} (hγ : (glueLat 1 1).form (glueIota 1 1 γ) (glueIota 1 1 γ) = 2)
    (c : ℂ) : Aut VN :=
  rootExp (glueLat 1 1) (glueLat_even 1 1) (glueLat_posDef 1 le_rfl 1) hγ
    (c * latCob (latP 1) (glueLat 1 1) (glueIota 1 1) γ)

section Root

variable {γ : (latP 1).carrier} (hγ : (glueLat 1 1).form (glueIota 1 1 γ) (glueIota 1 1 γ) = 2)
  (hγ' : (latP 1).form γ γ = 2) (c : ℂ)

/-- The `V_N` derivation of `GX`. -/
abbrev DN : Module.End ℂ (LatModuleGen (glueLat 1 1)) :=
  VN.zeroMode ((c * latCob (latP 1) (glueLat 1 1) (glueIota 1 1) γ) •
    latChargeGen (glueLat 1 1) (glueIota 1 1 γ)) 1

theorem DN_Phi (v : Sp) :
    DN (γ := γ) c (Phi v) = Phi (V1.zeroMode (c • latChargeGen (latP 1) γ) 1 v) := by
  rw [VertexOperatorAlgebra.zeroMode_apply, VertexOperatorAlgebra.zeroMode_apply,
    Phi_hom.map_smul, Phi_charge]

theorem DN_Psi (x : Sp) : DN (γ := γ) c (Psi x) = Psi ((c • Dpm γ) x) := by
  rw [VertexOperatorAlgebra.zeroMode_apply, ← Phi_charge, ← Psi_mode, map_smul]
  rfl

include hγ' in
theorem GX_Phi (u : Sp) :
    GX hγ c (Phi u) = Phi (rootExp (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) hγ' c u) := by
  rw [GX, rootExp_apply, rootExp_apply]
  symm
  exact expFun_map Phi _ _ (fun v => (DN_Phi c v).symm) u

theorem presR_GX : PresR (GX hγ c) := by
  intro x
  rw [GX, rootExp_apply]
  obtain ⟨N, hN⟩ := (isLocNilp_zeroMode_smul (glueLat 1 1) (glueLat_even 1 1)
    (glueLat_posDef 1 le_rfl 1) (form_self_ne_zero_of_two (glueLat 1 1) hγ)
    (c * latCob (latP 1) (glueLat 1 1) (glueIota 1 1) γ)) (Psi x)
  rw [expFun_eq_expSum _ hN, ← expSum_map Psi (fun v => (DN_Psi c v).symm)]
  exact ⟨_, rfl⟩

/-- The lift of the root exponential is the module exponential series. -/
theorem lift_GX {N : ℕ} {x : Sp} (hx : (Dpm γ ^ N) x = 0) :
    lift (GX hγ c) x = expSum (c • Dpm γ) N x := by
  apply Psi_inj
  rw [Psi_lift (presR_GX hγ c), GX, rootExp_apply]
  have hN : ((DN (γ := γ) c) ^ N) (Psi x) = 0 := by
    rw [← pow_map_comm Psi (fun v => (DN_Psi c v).symm), smul_pow, LinearMap.smul_apply, hx,
      smul_zero, map_zero]
  rw [expFun_eq_expSum _ hN, ← expSum_map Psi (fun v => (DN_Psi c v).symm)]

end Root

/-- `exp(c e₀)`-lift. -/
abbrev GE (c : ℂ) : Aut VN := GX root_pos c
/-- `exp(c f₀)`-lift. -/
abbrev GF (c : ℂ) : Aut VN := GX root_neg c

theorem GE_Phi (c : ℂ) (u : Sp) : GE c (Phi u) = Phi (expE c u) := GX_Phi root_pos latP1_root c u
theorem GF_Phi (c : ℂ) (u : Sp) : GF c (Phi u) = Phi (expF c u) := GX_Phi root_neg latP1_root' c u

/-! ## §5 The torus -/

/-- The character `x ↦ u^{x₀}` of the gluing lattice. -/
def chiG (u : ℂˣ) : (glueLat 1 1).carrier →+ Additive ℂˣ :=
  (zmultiplesHom (Additive ℂˣ) (Additive.ofMul u)).comp
    (Pi.evalAddMonoidHom (fun _ : Fin 2 => ℤ) 0)

theorem charVal_chiG (u : ℂˣ) (x : (glueLat 1 1).carrier) :
    charVal (glueLat 1 1) (chiG u) x = ((u ^ (x 0) : ℂˣ) : ℂ) := by
  show ((Additive.toMul ((x 0) • Additive.ofMul u) : ℂˣ) : ℂ) = _
  rw [toMul_zsmul, toMul_ofMul]

/-- The `V_N` torus element lifting `charU u`. -/
def GC (u : ℂˣ) : Aut VN :=
  charAut (glueLat 1 1) (chiG u) (glueLat_even 1 1) (glueLat_posDef 1 le_rfl 1)

theorem GC_latStateGen (u : ℂˣ) (p : FockN (rank (glueLat 1 1))) (x : (glueLat 1 1).carrier) :
    GC u (latStateGen (glueLat 1 1) p x) =
      ((u ^ (x 0) : ℂˣ) : ℂ) • latStateGen (glueLat 1 1) p x := by
  rw [GC, charAut_apply, charLat_latStateGen _ _ (glueLat_posDef 1 le_rfl 1), charVal_chiG]

theorem iota_zero (n : ℤ) : (glueIota 1 1 n + glueDelta 1 1) 0 = n := by
  rw [glueIota_apply, glueDelta]
  show (Pi.single (0 : Fin 2) n + Pi.single (1 : Fin 2) (1 : ℤ) : Fin 2 → ℤ) 0 = n
  simp

theorem iota_zero' (n : ℤ) : (glueIota 1 1 n) 0 = n := by
  rw [glueIota_apply]
  simp

theorem GC_Phi (u : ℂˣ) (v : Sp) : GC u (Phi v) = Phi (charU 1 le_rfl u v) := by
  have h : (GC u).toLinearEquiv.toLinearMap ∘ₗ Phi =
      Phi ∘ₗ (charU 1 le_rfl u).toLinearEquiv.toLinearMap := by
    refine LinearMap.ext_on_range (latStateGen_span (latP 1)) fun q => ?_
    obtain ⟨p, γ⟩ := q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [charU_latStateGen, map_smul, latMorph_latStateGen, map_smul, GC_latStateGen, iota_zero',
      smul_smul, smul_smul, mul_comm]
    rfl
  exact LinearMap.congr_fun h v

theorem presR_GC (u : ℂˣ) : PresR (GC u) := by
  intro x
  have hx : x ∈ (LinearMap.range Psi).comap ((GC u).toLinearEquiv.toLinearMap ∘ₗ Psi) := by
    have htop : Submodule.span ℂ (Set.range fun q : FockN (rank (latP 1)) × (latP 1).carrier =>
        latStateGen (latP 1) q.1 q.2) ≤
        (LinearMap.range Psi).comap ((GC u).toLinearEquiv.toLinearMap ∘ₗ Psi) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨p, n⟩, rfl⟩
      change GC u (Psi (latStateGen (latP 1) p n)) ∈ LinearMap.range Psi
      rw [shiftEmb_latStateGen, GC_latStateGen, ← shiftEmb_latStateGen]
      exact ⟨_, map_smul Psi _ _⟩
    rw [latStateGen_span] at htop
    exact htop trivial
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, hy⟩

/-- The torus lift acts by `u^n` on the charge-`n` sector. -/
theorem lift_GC (u : ℂˣ) (p : FockN (rank (latP 1))) (n : ℤ) :
    lift (GC u) (latStateGen (latP 1) p n) = ((u ^ n : ℂˣ) : ℂ) • latStateGen (latP 1) p n := by
  change PsiInv (GC u (Psi (latStateGen (latP 1) p n))) = _
  rw [shiftEmb_latStateGen, GC_latStateGen, iota_zero, ← shiftEmb_latStateGen, map_smul,
    PsiInv_Psi]

/-! ## §6 The cubic rotation and the Klein involution -/

/-- The lift of `rotC = rot2 * rot4`. -/
def GR : Aut VN := GE (I - 1) * GF eps1 * GE (-1 - I / 2) * GC unitHalf * GC unitI

theorem presR_GR : PresR GR :=
  presR_mul (presR_mul (presR_mul (presR_mul (presR_GX _ _) (presR_GX _ _)) (presR_GX _ _))
    (presR_GC _)) (presR_GC _)

theorem GR_Phi (u : Sp) : GR (Phi u) = Phi (rotC u) := by
  simp only [GR, rotC, rot2, rot4, Aut.mul_apply]
  rw [GC_Phi, GC_Phi, GE_Phi, GF_Phi, GE_Phi]

/-- The module lift of `rotC`. -/
def FR : Sp →ₗ[ℂ] Sp := lift GR

theorem FR_mode (u : Sp) (n : ℤ) (x : Sp) :
    FR (mode (Mo.YM u) n x) = mode (Mo.YM (rotC u)) n (FR x) :=
  lift_mode (α := rotC) presR_GR GR_Phi u n x

theorem FR_eq (x : Sp) :
    FR x = lift (GE (I - 1)) (lift (GF eps1) (lift (GE (-1 - I / 2))
      (lift (GC unitHalf) (lift (GC unitI) x)))) := by
  rw [FR, GR, lift_mul (presR_GC _), lift_mul (presR_GC _), lift_mul (presR_GX _ _),
    lift_mul (presR_GX _ _)]

/-- The module lift of the Klein element `charU (-1)`. -/
def CK : Sp →ₗ[ℂ] Sp := lift (GC (-1))

theorem CK_mode (u : Sp) (n : ℤ) (x : Sp) :
    CK (mode (Mo.YM u) n x) = mode (Mo.YM (charU 1 le_rfl (-1) u)) n (CK x) :=
  lift_mode (α := charU 1 le_rfl (-1)) (presR_GC _) (GC_Phi _) u n x

end VOA.Classification.COne.OrbRat6
