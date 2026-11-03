/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LeechLatticeVOA
import VOA.Modularity.Twisted

/-!
# The lattice involution `θ` and the fixed-point VOA `V_Λ⁺`  (Moonshine step M2)

For an even positive-definite lattice `L`, the isometry `-1` of `L` lifts to an automorphism `θ`
of the lattice VOA `V_L = FockN(rank L) ⊗ ℂ{L}` (`LatGen.latticeVOAGen`):

  `θ(p ⊗ e^α) = σ(p) ⊗ e^{-α}`,

where `σ` is the Fock-space algebra automorphism negating every oscillator `h_a(-n)` (FLM §10.4).
The FLM cocycle `ε = latticeCocycle` is a bimultiplicative sign, so `ε(-α,-β) = ε(α,β)`
(`latticeCocycle_neg_neg`) and **no sign correction is needed** in the lift.

## Proof route for the intertwining property

`YfullGen` is produced by `Reconstruction.reconstruct` and is determined (by linearity) by its
values `YfullGen_word` on the spanning word states `wordStateLatGen l α`
(`wordStateLatGen_span`).  So no Goddard-uniqueness argument is needed: it suffices to conjugate
the word fields.
* `Intertw g c A B` (`g A(z) = c·B(z) g`) is closed under normal-ordered products (`Intertw.nprod`),
  `∂_z` and scalars;
* `σ` intertwines `E^±(α,z)` with `E^±(-α,z)` (`sigmaN_vSchur`, `sigmaN_aExpVec`), hence
  `θ Y(e^α,z) θ = Y(e^{-α},z)` (`thetaLat_Yeαvec`), and `θ h_a(z) θ = -h_a(z)` including the
  momentum zero mode (`thetaLat_alphaLatGen`);
* by induction on the word, `θ Y_word(l,α) θ = (-1)^{|l|} Y_word(l,-α)` (`thetaLat_YwordLatGen`),
  matching `θ(wordState l α) = (-1)^{|l|} wordState l (-α)` (`thetaLat_wordStateLatGen`).

## Main declarations
* `LatGen.sigmaN` — the Fock involution, with `sigmaN_oscN`, `sigmaN_mem_gradingZN`.
* `LatGen.thetaLat` — `θ : V_L ≃ₗ V_L`, with `thetaLat_tmul`, `thetaLat_involutive`,
  `thetaLat_vacuum`, `thetaLat_omega`, `thetaLat_mem_gradingLatGen`.
* `LatGen.thetaLat_YfullGen`, `LatGen.thetaLat_mode` — `θ(u₍ₙ₎v) = (θu)₍ₙ₎(θv)`.
* `LatGen.thetaAut` — `θ ∈ Aut(V_L)`, with `thetaAut_sq` and `thetaAut_ne_one` (for `L ≠ 0`).
* `Moonshine.leechTheta`, `Moonshine.leechVOAPlus` — the Leech specialization and the fixed-point
  VOA `V_Λ⁺ = V_Λ^{⟨θ⟩}` (via `orbifoldVOA`), with `leechVOAPlus_centralCharge : c = 24` and
  `mem_leechVOAPlus_iff`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
(no `VOA.pbw`).  Unconditional given `hEven`/`hPos`.  Not done in this file: the `θ`-twisted
`V_Λ`-module and the `ℤ/2`-orbifold `V♮ = V_Λ⁺ ⊕ (V_Λ^T)⁺` (later Moonshine steps).

## References
* Frenkel–Lepowsky–Meurman, *Vertex Operator Algebras and the Monster*, §10.4; Gannon §5.3.6.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN MvPolynomial

/-! ## §1  The Fock involution `σ : h_a(-n) ↦ -h_a(-n)`. -/

section Fock

variable (r : ℕ)

/-- The algebra endomorphism of `FockN r` negating every oscillator variable. -/
noncomputable def sigmaAlg : FockN r →ₐ[ℂ] FockN r := MvPolynomial.aeval (fun v => -(X v : FockN r))

@[simp] theorem sigmaAlg_X (v : ℕ × Fin r) : sigmaAlg r (X v) = -X v := by
  rw [sigmaAlg, MvPolynomial.aeval_X]

theorem sigmaAlg_involutive : Function.Involutive (sigmaAlg r) := by
  have h : (sigmaAlg r).comp (sigmaAlg r) = AlgHom.id ℂ (FockN r) :=
    MvPolynomial.algHom_ext fun v => by
      rw [AlgHom.comp_apply, sigmaAlg_X, map_neg, sigmaAlg_X, neg_neg, AlgHom.id_apply]
  intro p
  exact congrArg (fun f : FockN r →ₐ[ℂ] FockN r => f p) h

/-- The **Fock involution** `σ` as a `ℂ`-linear equivalence. -/
noncomputable def sigmaN : FockN r ≃ₗ[ℂ] FockN r :=
  LinearEquiv.ofInvolutive (sigmaAlg r).toLinearMap (sigmaAlg_involutive r)

theorem sigmaN_apply (p : FockN r) : sigmaN r p = sigmaAlg r p := rfl

theorem sigmaN_mul (p q : FockN r) : sigmaN r (p * q) = sigmaN r p * sigmaN r q :=
  map_mul (sigmaAlg r) p q

@[simp] theorem sigmaN_X (v : ℕ × Fin r) : sigmaN r (X v) = -X v := sigmaAlg_X r v

theorem sigmaN_one : sigmaN r 1 = 1 := map_one (sigmaAlg r)

theorem sigmaN_sigmaN (p : FockN r) : sigmaN r (sigmaN r p) = p := sigmaAlg_involutive r p

theorem sigmaN_pderiv (v : ℕ × Fin r) (p : FockN r) :
    sigmaN r (pderiv v p) = -pderiv v (sigmaN r p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [pderiv_C, map_zero, sigmaN_apply, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        MvPolynomial.algebraMap_eq, pderiv_C, neg_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, neg_add]
  | mul_X p w hp =>
      rw [pderiv_mul, map_add, sigmaN_mul, sigmaN_mul, hp, sigmaN_X, pderiv_X]
      have hδ : sigmaN r ((Pi.single v 1 : ℕ × Fin r → FockN r) w) =
          (Pi.single v 1 : ℕ × Fin r → FockN r) w := by
        by_cases h : w = v
        · subst h; rw [Pi.single_eq_same, sigmaN_one]
        · rw [Pi.single_eq_of_ne h, map_zero]
      rw [hδ, sigmaN_mul, sigmaN_X, pderiv_mul, Derivation.map_neg, pderiv_X]
      ring

/-- `σ` anticommutes with every oscillator: `σ aᵃₙ = -aᵃₙ σ`. -/
theorem sigmaN_oscN (k : ℂ) (a : Fin r) (n : ℤ) (p : FockN r) :
    sigmaN r (oscN r k a n p) = -oscN r k a n (sigmaN r p) := by
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [oscN_apply_neg r k a hn, oscN_apply_neg r k a hn, sigmaN_mul, sigmaN_X, neg_mul]
  · subst hn; rw [oscN_zero, LinearMap.zero_apply, LinearMap.zero_apply, map_zero, neg_zero]
  · rw [oscN_apply_pos r k a hn, oscN_apply_pos r k a hn, map_smul, map_smul, sigmaN_pderiv,
      smul_neg, smul_neg]

theorem sigmaN_monomial_mem (d : (ℕ × Fin r) →₀ ℕ) :
    sigmaN r (monomial d 1) ∈ gradingWN r (Finsupp.weight weightFnN d) := by
  rw [sigmaN_apply, sigmaAlg, MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod,
    mem_gradingWN, Finsupp.weight_apply, Finsupp.sum]
  exact IsWeightedHomogeneous.prod _ _ _ fun i _ =>
    ((weightedHomogeneousSubmodule ℂ weightFnN _).neg_mem
      (isWeightedHomogeneous_X ℂ weightFnN i)).pow _

/-- `σ` preserves the Fock weight grading. -/
theorem sigmaN_mem_gradingWN {w : ℕ} {p : FockN r} (hp : p ∈ gradingWN r w) :
    sigmaN r p ∈ gradingWN r w := by
  have hp' := gradingWN_le_span r w hp
  clear hp
  induction hp' using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd, rfl⟩ := hx
      have h := sigmaN_monomial_mem r d
      rwa [show Finsupp.weight weightFnN d = w from hd] at h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem sigmaN_mem_gradingZN (n : ℤ) {p : FockN r} (hp : p ∈ gradingZN r n) :
    sigmaN r p ∈ gradingZN r n := by
  by_cases hn : 0 ≤ n
  · rw [gradingZN_of_nonneg hn] at hp ⊢; exact sigmaN_mem_gradingWN r hp
  · rw [gradingZN_of_neg (by omega), Submodule.mem_bot] at hp ⊢; rw [hp, map_zero]

end Fock

/-! ## §2  The intertwining calculus for formal distributions. -/

section Intertw

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- `g A(z) = c · B(z) g`, coefficientwise. -/
def Intertw (g : End ℂ V) (c : ℂ) (A B : FormalDist (End ℂ V)) : Prop :=
  ∀ (t : ℤ) (x : V), g (A t x) = c • B t (g x)

theorem Intertw.nprod {g : End ℂ V} {c d : ℂ} {a a' b b' : FormalDist (End ℂ V)}
    (ha : IsField a) (hb : IsField b) (ha' : IsField a') (hb' : IsField b')
    (hA : Intertw g c a a') (hB : Intertw g d b b') :
    Intertw g (c * d) (VOA.nprod ha hb) (VOA.nprod ha' hb') := by
  intro s x
  rw [nprod_apply, nprod_apply,
    smul_finsum' _ (normalOrdered_diag_support_finite ha' hb' s (g x))]
  refine (g.toAddMonoidHom.map_finsum (normalOrdered_diag_support_finite ha hb s x)).trans ?_
  refine finsum_congr fun m => ?_
  change g (normalOrdered a b m (s - m) x) = (c * d) • normalOrdered a' b' m (s - m) (g x)
  rw [normalOrdered_apply, normalOrdered_apply]
  split_ifs
  · rw [Module.End.mul_apply, Module.End.mul_apply, hA, hB, map_smul, smul_smul]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hB, hA, map_smul, smul_smul, mul_comm d c]

theorem Intertw.deriv {g : End ℂ V} {c : ℂ} {A B : FormalDist (End ℂ V)} (h : Intertw g c A B) :
    Intertw g c (VOA.deriv A) (VOA.deriv B) := by
  intro t x
  rw [deriv_apply, deriv_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_zsmul, h,
    smul_comm]

theorem Intertw.deriv_iterate {g : End ℂ V} {c : ℂ} {A B : FormalDist (End ℂ V)}
    (h : Intertw g c A B) (i : ℕ) : Intertw g c (VOA.deriv^[i] A) (VOA.deriv^[i] B) := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ih.deriv

theorem Intertw.const_smul {g : End ℂ V} {c : ℂ} {A B : FormalDist (End ℂ V)} (h : Intertw g c A B)
    (e : ℂ) : Intertw g c (e • A) (e • B) := by
  intro t x
  change g ((e • A t) x) = c • (e • B t) (g x)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h, smul_comm]

end Intertw

/-! ## §3  `σ` on the charge machinery: `σ ∘ X(α) = X(-α) ∘ σ`. -/

section Charge

variable (L : IntegralLattice)

theorem orthCoord_neg (α : L.carrier) : orthCoord L (-α) = -orthCoord L α := by
  have hc : coordR L (-α) = -coordR L α := by
    funext i
    simp only [coordR, coord, map_neg, Finsupp.neg_apply, Int.cast_neg, Pi.neg_apply]
  rw [orthCoord, orthCoord, hc, Matrix.mulVec_neg]

theorem chargeCoord_neg (α : L.carrier) (b : Fin (rank L)) :
    chargeCoord L (-α) b = -chargeCoord L α b := by
  rw [chargeCoord, chargeCoord, orthCoord_neg, Pi.neg_apply, Complex.ofReal_neg]

theorem chargeOsc_neg (α : L.carrier) (m : ℤ) : chargeOsc L (-α) m = -chargeOsc L α m := by
  rw [chargeOsc, chargeOsc, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [orthCoord_neg, Pi.neg_apply, Complex.ofReal_neg, neg_smul]

theorem sigmaN_chargeOsc (α : L.carrier) (m : ℤ) (p : FockN (rank L)) :
    sigmaN (rank L) (chargeOsc L α m p) = chargeOsc L (-α) m (sigmaN (rank L) p) := by
  rw [chargeOsc_neg, LinearMap.neg_apply]
  simp only [chargeOsc, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum,
    map_smul, sigmaN_oscN, smul_neg, Finset.sum_neg_distrib]

theorem sigmaN_vVar (α : L.carrier) (m : ℕ) :
    sigmaN (rank L) (vVar L α m) = vVar L (-α) m := by
  rw [vVar, vVar, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, sigmaN_X, chargeCoord_neg, smul_neg, neg_smul]

theorem sigmaN_vSchur (α : L.carrier) (N : ℕ) :
    sigmaN (rank L) (vSchur L α N) = vSchur L (-α) N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    match N with
    | 0 => rw [vSchur_zero, vSchur_zero, sigmaN_one]
    | (M+1) =>
      rw [vSchur_succ, vSchur_succ, map_smul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [sigmaN_mul, sigmaN_vVar, ih (M - m) (by simp at hm; omega)]

theorem sigmaN_aExpVec (α : L.carrier) (N : ℕ) (p : FockN (rank L)) :
    sigmaN (rank L) (aExpVec L α N p) = aExpVec L (-α) N (sigmaN (rank L) p) := by
  induction N using Nat.strong_induction_on generalizing p with
  | _ N ih =>
    match N with
    | 0 => rw [aExpVec_zero, aExpVec_zero, LinearMap.id_apply, LinearMap.id_apply]
    | (M+1) =>
      rw [aExpVec_succ, aExpVec_succ, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
        LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.neg_apply,
        map_neg, sigmaN_chargeOsc, ih (M - m) (by simp at hm; omega)]

theorem sigmaN_EminusVecField (α : L.carrier) :
    Intertw (sigmaN (rank L)).toLinearMap 1 (EminusVecField L α) (EminusVecField L (-α)) := by
  intro t x
  rw [one_smul, EminusVecField_apply, EminusVecField_apply]
  split_ifs
  · rw [EminusVec, EminusVec, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
      LinearEquiv.coe_coe, sigmaN_mul, sigmaN_vSchur]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem sigmaN_EplusVecField (α : L.carrier) :
    Intertw (sigmaN (rank L)).toLinearMap 1 (EplusVecField L α) (EplusVecField L (-α)) := by
  intro t x
  rw [one_smul, EplusVecField_apply, EplusVecField_apply]
  split_ifs
  · rw [LinearEquiv.coe_coe, sigmaN_aExpVec]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

theorem sigmaN_EEVec (α : L.carrier) :
    Intertw (sigmaN (rank L)).toLinearMap 1 (EEVec L α) (EEVec L (-α)) := by
  have h := Intertw.nprod (EminusVecField_isField L α) (EplusVecField_isField L α)
    (EminusVecField_isField L (-α)) (EplusVecField_isField L (-α))
    (sigmaN_EminusVecField L α) (sigmaN_EplusVecField L α)
  rwa [mul_one] at h

theorem sigmaN_wordStateN (l : List (ℕ × Fin (rank L))) :
    sigmaN (rank L) (wordStateN l) = ((-1 : ℂ) ^ l.length) • wordStateN l := by
  induction l with
  | nil => rw [wordStateN_nil, sigmaN_one, List.length_nil, pow_zero, one_smul]
  | cons ia rest ih =>
      rw [wordStateN_cons, sigmaN_mul, sigmaN_X, ih, List.length_cons, pow_succ',
        mul_smul, mul_smul_comm, neg_mul, neg_one_smul, smul_neg]

theorem latticeCocycle_neg_left (α β : L.carrier) :
    latticeCocycle L (-α) β = latticeCocycle L α β := by
  have h := latticeCocycle_add_left L α (-α) β
  rw [add_neg_cancel, latticeCocycle_zero_left] at h
  calc latticeCocycle L (-α) β
      = (latticeCocycle L α β * latticeCocycle L α β) * latticeCocycle L (-α) β := by
        rw [latticeCocycle_sq, one_mul]
    _ = latticeCocycle L α β * 1 := by rw [h, mul_assoc]
    _ = latticeCocycle L α β := mul_one _

theorem latticeCocycle_neg_right (α β : L.carrier) :
    latticeCocycle L α (-β) = latticeCocycle L α β := by
  have h := latticeCocycle_add_right L α β (-β)
  rw [add_neg_cancel, latticeCocycle_zero_right] at h
  calc latticeCocycle L α (-β)
      = (latticeCocycle L α β * latticeCocycle L α β) * latticeCocycle L α (-β) := by
        rw [latticeCocycle_sq, one_mul]
    _ = latticeCocycle L α β * 1 := by rw [h, mul_assoc]
    _ = latticeCocycle L α β := mul_one _

/-- The FLM cocycle is invariant under `(α,β) ↦ (-α,-β)`: no sign correction is needed for the
lift of `-1`. -/
theorem latticeCocycle_neg_neg (α β : L.carrier) :
    latticeCocycle L (-α) (-β) = latticeCocycle L α β := by
  rw [latticeCocycle_neg_left, latticeCocycle_neg_right]

end Charge

/-! ## §4  The lattice involution `θ = σ ⊗ (e^α ↦ e^{-α})`. -/

section Theta

variable (L : IntegralLattice)

/-- The **canonical lift `θ` of the lattice involution `-1`** to `V_L`:
`θ(p ⊗ e^α) = σ(p) ⊗ e^{-α}`. -/
noncomputable def thetaLat : LatModuleGen L ≃ₗ[ℂ] LatModuleGen L :=
  TensorProduct.congr (sigmaN (rank L)) (Finsupp.domLCongr (Equiv.neg L.carrier))

theorem thetaLat_tmul (p : FockN (rank L)) (α : L.carrier) :
    thetaLat L (p ⊗ₜ[ℂ] eGen L α) = sigmaN (rank L) p ⊗ₜ[ℂ] eGen L (-α) := by
  rw [thetaLat, TensorProduct.congr_tmul]
  congr 1
  rw [eGen, eGen, Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]
  rfl

theorem thetaLat_latStateGen (p : FockN (rank L)) (α : L.carrier) :
    thetaLat L (latStateGen L p α) = latStateGen L (sigmaN (rank L) p) (-α) :=
  thetaLat_tmul L p α

/-- `θ² = 1`. -/
theorem thetaLat_involutive : Function.Involutive (thetaLat L) := by
  intro x
  have h : (thetaLat L).toLinearMap ∘ₗ (thetaLat L).toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range (latStateGen_span L) fun q => ?_
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, thetaLat_latStateGen,
      thetaLat_latStateGen, sigmaN_sigmaN, neg_neg, LinearMap.id_apply]
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] LatModuleGen L => f x) h

theorem thetaLat_thetaLat (x : LatModuleGen L) : thetaLat L (thetaLat L x) = x :=
  thetaLat_involutive L x

theorem thetaLat_symm : (thetaLat L).symm = thetaLat L := by
  ext x
  rw [LinearEquiv.symm_apply_eq, thetaLat_thetaLat]

/-- `θ` fixes the vacuum. -/
theorem thetaLat_vacuum : thetaLat L (latVacuumGen L) = latVacuumGen L := by
  rw [latVacuumGen, thetaLat_latStateGen, vacuumN, sigmaN_one, neg_zero]

/-- `θ` fixes the conformal vector (`ω` is quadratic in the oscillators). -/
theorem thetaLat_omega : thetaLat L (omegaLatGen L) = omegaLatGen L := by
  rw [omegaLatGen, mkEα_apply, thetaLat_tmul, neg_zero]
  congr 1
  rw [ωN, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ωNa, map_smul, sigmaN_oscN, sigmaN_oscN, map_neg, neg_neg, vacuumN, sigmaN_one]

/-- `θ` maps the bigraded piece `(w, α)` onto `(w, -α)`. -/
theorem thetaLat_mem_bigradα {w : ℤ} {α : L.carrier} {x : LatModuleGen L}
    (hx : x ∈ bigradα L (w, α)) : thetaLat L x ∈ bigradα L (w, -α) := by
  obtain ⟨p, hp, rfl⟩ := hx
  refine ⟨sigmaN (rank L) p, ?_, ?_⟩
  · exact sigmaN_mem_gradingZN _ _ hp
  · rw [mkEα_apply, mkEα_apply, thetaLat_tmul]

theorem halfNorm_neg (α : L.carrier) : halfNorm L (-α) = halfNorm L α := by
  simp [halfNorm]

/-- `θ` preserves the `L₀`-grading. -/
theorem thetaLat_mem_gradingLatGen {k : ℤ} {x : LatModuleGen L} (hx : x ∈ gradingLatGen L k) :
    thetaLat L x ∈ gradingLatGen L k := by
  rw [gradingLatGen] at hx ⊢
  refine Submodule.iSup_induction _ (motive := fun x => thetaLat L x ∈ _) hx (fun α y hy => ?_)
    (by simp only [map_zero]; exact Submodule.zero_mem _)
    (fun y z hy hz => by simp only [map_add]; exact Submodule.add_mem _ hy hz)
  have h := thetaLat_mem_bigradα L hy
  rw [← halfNorm_neg L α] at h
  exact Submodule.mem_iSup_of_mem (-α) h

/-! ### Intertwining the vertex operators -/

theorem intertw_of_latState {c : ℂ} {A B : FormalDist (End ℂ (LatModuleGen L))}
    (h : ∀ (t : ℤ) (p : FockN (rank L)) (β : L.carrier),
      thetaLat L (A t (latStateGen L p β)) = c • B t (thetaLat L (latStateGen L p β))) :
    Intertw (thetaLat L).toLinearMap c A B := by
  intro t x
  have hext : (thetaLat L).toLinearMap ∘ₗ A t = (c • B t) ∘ₗ (thetaLat L).toLinearMap :=
    LinearMap.ext_on_range (latStateGen_span L) fun q => h t q.1 q.2
  exact congrArg (fun f : LatModuleGen L →ₗ[ℂ] LatModuleGen L => f x) hext

/-- `θ Y(e^α,z) θ⁻¹ = Y(e^{-α},z)`. -/
theorem thetaLat_Yeαvec (α : L.carrier) :
    Intertw (thetaLat L).toLinearMap 1 (Yeαvec L α) (Yeαvec L (-α)) := by
  refine intertw_of_latState L fun t p β => ?_
  have hE := sigmaN_EEVec L α (t - L.form α β) p
  rw [one_smul] at hE
  rw [one_smul, Yeαvec_tmul, map_smul, thetaLat_latStateGen, thetaLat_latStateGen, Yeαvec_tmul,
    latticeCocycle_neg_neg, show L.form (-α) (-β) = L.form α β by simp, neg_add]
  congr 2

/-- `θ h_a(z) θ⁻¹ = -h_a(z)` (including the momentum zero mode). -/
theorem thetaLat_alphaLatGen (a : Fin (rank L)) :
    Intertw (thetaLat L).toLinearMap (-1) (alphaLatGen L a) (alphaLatGen L a) := by
  refine intertw_of_latState L fun t p β => ?_
  rw [alphaLatGen_apply, LinearMap.add_apply, LinearMap.add_apply, thetaLat_latStateGen]
  have hr : ∀ (q : FockN (rank L)) (γ : L.carrier), LinearMap.rTensor (L.carrier →₀ ℂ)
      (currentN (rank L) 1 a t) (latStateGen L q γ) = latStateGen L (oscN (rank L) 1 a (-t - 1) q) γ :=
    fun q γ => by rw [latStateGen, LinearMap.rTensor_tmul, currentN_apply]; rfl
  rw [hr, hr, map_add, thetaLat_latStateGen, sigmaN_oscN]
  split_ifs
  · rw [zGradeOpGen_latStateGen, zGradeOpGen_latStateGen, map_smul, thetaLat_latStateGen,
      chargeCoord_neg, latStateGen, latStateGen, latStateGen, TensorProduct.neg_tmul]
    module
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero, add_zero, add_zero, latStateGen,
      latStateGen, TensorProduct.neg_tmul, neg_one_smul]

theorem thetaLat_genFieldLatGen (a : Fin (rank L)) (i : ℕ) :
    Intertw (thetaLat L).toLinearMap (-1) (genFieldLatGen L a i) (genFieldLatGen L a i) :=
  ((thetaLat_alphaLatGen L a).deriv_iterate i).const_smul _

/-- `θ Y_word(l,α) θ⁻¹ = (-1)^{|l|} Y_word(l,-α)`. -/
theorem thetaLat_YwordLatGen (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    Intertw (thetaLat L).toLinearMap ((-1 : ℂ) ^ l.length) (YwordLatGen L l α)
      (YwordLatGen L l (-α)) := by
  induction l with
  | nil => rw [List.length_nil, pow_zero, YwordLatGen_nil, YwordLatGen_nil]; exact thetaLat_Yeαvec L α
  | cons ia rest ih =>
      rw [YwordLatGen_cons, YwordLatGen_cons, List.length_cons, pow_succ']
      exact Intertw.nprod _ _ _ _ (thetaLat_genFieldLatGen L ia.2 ia.1) ih

theorem thetaLat_wordStateLatGen (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    thetaLat L (wordStateLatGen L l α) = ((-1 : ℂ) ^ l.length) • wordStateLatGen L l (-α) := by
  rw [wordStateLatGen_eq, wordStateLatGen_eq, thetaLat_tmul, sigmaN_wordStateN,
    TensorProduct.smul_tmul']

end Theta

/-! ## §5  `θ` is an automorphism of the lattice VOA. -/

section Aut

variable (L : IntegralLattice) (hEven : L.Even) (hPos : L.PosDef)

/-- **`θ` intertwines the reconstructed vertex map**: `θ Y(u,z) θ⁻¹ = Y(θu,z)`, coefficientwise.
Proved on the spanning word states (`YfullGen_word`, `thetaLat_YwordLatGen`) and extended by
linearity. -/
theorem thetaLat_YfullGen (u : LatModuleGen L) (t : ℤ) (x : LatModuleGen L) :
    thetaLat L (YfullGen L hEven hPos u t x)
      = YfullGen L hEven hPos (thetaLat L u) t (thetaLat L x) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (Function.uncurry (wordStateLatGen L))) := by
    rw [wordStateLatGen_span]; trivial
  induction hu using Submodule.span_induction generalizing x with
  | mem w hw =>
      obtain ⟨⟨l, α⟩, rfl⟩ := hw
      simp only [Function.uncurry_apply_pair]
      rw [YfullGen_word, thetaLat_wordStateLatGen, map_smul, YfullGen_word]
      exact thetaLat_YwordLatGen L l α t x
  | zero => simp only [map_zero]; rfl
  | add v w _ _ hv hw =>
      simp only [map_add]
      change thetaLat L (YfullGen L hEven hPos v t x + YfullGen L hEven hPos w t x) =
        YfullGen L hEven hPos (thetaLat L v) t (thetaLat L x)
          + YfullGen L hEven hPos (thetaLat L w) t (thetaLat L x)
      rw [map_add, hv, hw]
  | smul c v _ hv =>
      simp only [map_smul]
      change thetaLat L (c • YfullGen L hEven hPos v t x) =
        c • YfullGen L hEven hPos (thetaLat L v) t (thetaLat L x)
      rw [map_smul, hv]

/-- The mode form: `θ(u₍ₙ₎v) = (θu)₍ₙ₎(θv)`. -/
theorem thetaLat_mode (u : LatModuleGen L) (n : ℤ) (v : LatModuleGen L) :
    thetaLat L (mode (YfullGen L hEven hPos u) n v)
      = mode (YfullGen L hEven hPos (thetaLat L u)) n (thetaLat L v) := by
  rw [mode_apply, mode_apply]
  exact thetaLat_YfullGen L hEven hPos u _ v

/-- **The lattice involution `θ` as a VOA automorphism** of `V_L`. -/
noncomputable def thetaAut : Aut (latticeVOAGen L hEven hPos) where
  toLinearEquiv := thetaLat L
  map_smul' u n v := thetaLat_mode L hEven hPos u n v
  map_vacuum := thetaLat_vacuum L
  map_omega := thetaLat_omega L

@[simp] theorem thetaAut_apply (v : LatModuleGen L) : thetaAut L hEven hPos v = thetaLat L v := rfl

/-- `θ² = 1` in `Aut(V_L)`. -/
theorem thetaAut_sq : thetaAut L hEven hPos * thetaAut L hEven hPos = 1 :=
  Aut.ext (LinearEquiv.ext fun x => thetaLat_thetaLat L x)

/-- `θ` acts on the charged vacua by `e^α ↦ e^{-α}`. -/
theorem thetaLat_latChargeGen (α : L.carrier) :
    thetaLat L (latChargeGen L α) = latChargeGen L (-α) := by
  rw [latChargeGen, thetaLat_latStateGen, vacuumN, sigmaN_one]; rfl

/-- `θ ≠ 1` as soon as `L ≠ 0`. -/
theorem thetaAut_ne_one (hL : ∃ α : L.carrier, α ≠ 0) : thetaAut L hEven hPos ≠ 1 := by
  obtain ⟨α, hα⟩ := hL
  intro h
  have h1 : thetaLat L (latChargeGen L α) = latChargeGen L α := by
    have := congrArg (fun g : Aut (latticeVOAGen L hEven hPos) => g (latChargeGen L α)) h
    simpa using this
  rw [thetaLat_latChargeGen] at h1
  have h2 := congrArg (coordEα L α) h1
  rw [latChargeGen, latChargeGen, latStateGen, latStateGen, coordEα_apply, coordEα_apply,
    if_pos rfl] at h2
  by_cases hneg : α = -α
  · have h2α : (2 : ℤ) • α = 0 := by
      rw [two_smul]; nth_rewrite 2 [hneg]; exact add_neg_cancel α
    exact hα ((smul_eq_zero.mp h2α).resolve_left two_ne_zero)
  · rw [if_neg hneg, vacuumN] at h2
    exact one_ne_zero h2.symm

end Aut

end VOA.LatGen

namespace VOA

/-- Membership in the fixed points of a cyclic group: `v ∈ 𝒱^⟨g⟩ ↔ g v = v`. -/
theorem mem_orbifold_zpowers_iff {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VertexOperatorAlgebra 𝒱} (g : Aut W) (v : 𝒱) :
    v ∈ (orbifold (Subgroup.zpowers g)).carrier ↔ g v = v := by
  constructor
  · intro hv; exact hv g (Subgroup.mem_zpowers g)
  · intro hv
    let S : Subgroup (Aut W) :=
      { carrier := {h | h v = v}
        mul_mem' := fun {a b} ha hb => by
          change a (b v) = v
          rw [show b v = v from hb]; exact ha
        one_mem' := rfl
        inv_mem' := fun {a} ha => by
          change a.toLinearEquiv.symm v = v
          rw [LinearEquiv.symm_apply_eq]; exact ha.symm }
    have hS : Subgroup.zpowers g ≤ S := (Subgroup.zpowers_le).mpr hv
    exact fun h hh => hS hh

namespace Moonshine

open LatGen

/-- The canonical lift `θ` of `-1 ∈ Aut(Λ)` to the Leech lattice VOA. -/
noncomputable def leechTheta : Aut leechVOA := thetaAut leech leech_even leech_posDef

theorem leechTheta_sq : leechTheta * leechTheta = 1 := thetaAut_sq leech leech_even leech_posDef

theorem leechTheta_ne_one : leechTheta ≠ 1 := by
  haveI : Nontrivial leech.carrier :=
    Module.nontrivial_of_finrank_pos (R := ℤ) (by
      have h : Module.finrank ℤ leech.carrier = 24 := leech_rank
      rw [h]; norm_num)
  obtain ⟨α, hα⟩ := exists_ne (0 : leech.carrier)
  exact thetaAut_ne_one leech leech_even leech_posDef ⟨α, hα⟩

/-- **The θ-fixed subVOA `V_Λ⁺ = V_Λ^{⟨θ⟩}`**, as a vertex operator algebra (the orbifold of the
cyclic group generated by `leechTheta`). -/
noncomputable def leechVOAPlus :
    VertexOperatorAlgebra (orbifold (Subgroup.zpowers leechTheta)).carrier :=
  orbifoldVOA (Subgroup.zpowers leechTheta)

theorem mem_leechVOAPlus_iff (v : LatModuleGen leech) :
    v ∈ (orbifold (Subgroup.zpowers leechTheta)).carrier ↔ thetaLat leech v = v :=
  mem_orbifold_zpowers_iff leechTheta v

/-- `c(V_Λ⁺) = 24`. -/
theorem leechVOAPlus_centralCharge : leechVOAPlus.centralCharge = 24 := by
  rw [leechVOAPlus, orbifoldVOA_centralCharge, leechVOA_centralCharge]

end Moonshine

end VOA
