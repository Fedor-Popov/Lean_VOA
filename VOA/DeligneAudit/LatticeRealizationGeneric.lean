/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.AffineGeneral.CartanLatticeSimple
import VOA.Moonshine.TrialitySl2
import VOA.Moonshine.TrialityTheta
import VOA.Moonshine.LatticeMorphRigid
import VOA.Examples.LatticeCharge
import VOA.Core.DeformationLiftedModes
import VOA.DeligneAudit.D4FusionKernelGeneric

/-!
# The lattice realization of `D(1, Nθ)`: the relations half, for any lattice and any sector

the `DeligneFusionLattice` (A₂, by hand) made generic.  For an even positive-definite lattice `L`, the lattice
VOA `W = V_L` and sector data `S`:

* `latRepG`: weight-one states `X i ∈ W₁` whose `0`-products are the sector table,
  `X_c (0) X_d = Σₑ f(c,d,e) X_e`, give a `CurrentModule S.f (LatModuleGen L)` (`op c n = (X_c)₍ₙ₎`);
* `LatData S L`: such a family together with, for every index, either a root `rt i` and a scalar (`X i ∈ ℂ e^{rt i}`)
  or a coroot vector (`X i = cv i (-1)𝟙`), and a root `θ`, subject to sign conditions on `⟨·, θ⟩` that are decidable
  per type;
* `LatData.sat`: **`e^{Nθ}` satisfies `ravFam S N 0`** (the relations of `M_{N,0}`), the relations half of
  `DemazureRealizationG S (ravFam S) Dem N`.  The raising relations and the truncations are vertex-operator
  vanishing `e^α₍ₙ₎e^β = 0` for `n ≥ -⟨α,β⟩` (`mode_ch_ch_zero`); the lowering relations are the weight shell
  (`eq_zero_of_charge_grading`): after `N·θ(hᵢ)+1` steps the charge `Nθ + k αᵢ` has `|·|²/2 > N²`.
-/

namespace VOA.DeligneAudit.LatticeRealization

open VOA VOA.LatGen VOA.LatGen.Screen VOA.IntegralLattice HeisenbergN
open VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.DeligneSector VOA.DeligneAudit.UnivG

noncomputable section

variable (L : IntegralLattice) (hE : L.Even) (hP : L.PosDef)

/-- The lattice VOA `V_L`. -/
abbrev WL : VertexOperatorAlgebra (LatModuleGen L) := latticeVOAGen L hE hP

theorem form_comm' (v w : L.carrier) : L.form v w = L.form w v :=
  LinearMap.BilinForm.isSymm_def.mp L.isSymm v w

/-! ## The current module -/

theorem smul_one_vacG {x y : LatModuleGen L} (hx : x ∈ (WL L hE hP).grading 1)
    (hy : y ∈ (WL L hE hP).grading 1) : ∃ β : ℂ, (WL L hE hP).smul x 1 y = β • (WL L hE hP).vacuum := by
  have h := (WL L hE hP).grading_mode x hx y hy 1
  rw [show (1 : ℤ) + 1 - 1 - 1 = 0 by norm_num] at h
  change _ ∈ gradingLatGen L 0 at h
  rw [gradingLatGen_zero_eq_span_vacuum L hE hP, Submodule.mem_span_singleton] at h
  obtain ⟨β, hβ⟩ := h
  exact ⟨β, hβ.symm⟩

variable {L hE hP}

/-- **The current module of a weight-one family with the sector bracket.** -/
def latRepG (S : DeligneSectorData) (X : Fin S.n → LatModuleGen L)
    (hX : ∀ i, X i ∈ (WL L hE hP).grading 1)
    (hbr : ∀ c d, (WL L hE hP).smul (X c) 0 (X d) = ∑ e, S.f c d e • X e) :
    CurrentModule S.f (LatModuleGen L) where
  op c n := mode ((WL L hE hP).Y (X c)) (n : ℤ)
  comm c d r s v := by
    obtain ⟨β, hβ⟩ := smul_one_vacG L hE hP (hX c) (hX d)
    have h := VOA.Deform.current_mode_commutator (W := WL L hE hP) (hX c) (hX d) β hβ v r s
    change (WL L hE hP).smul (X c) r ((WL L hE hP).smul (X d) s v) -
      (WL L hE hP).smul (X d) s ((WL L hE hP).smul (X c) r v) = _
    rw [h, hbr, smul_sum_left]
    have hz : (if ((r : ℤ) + (s : ℤ)) = 0 then (((r : ℤ) : ℂ) * β) • v else 0) = 0 := by
      split_ifs with h0
      · have : (r : ℤ) = 0 := by omega
        rw [this]; simp
      · rfl
    rw [hz, add_zero]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [PreVertexAlgebra.smul_smul_left]
    push_cast; rfl

/-! ## Vanishing tools (for any lattice) -/

variable (L) in
theorem gradingLatGen_le_ker_coordEαG {β : L.carrier} {k : ℤ} (hk : k < halfNorm L β) :
    gradingLatGen L k ≤ LinearMap.ker (coordEα L β) := by
  refine iSup_le fun α => ?_
  by_cases hα : α = β
  · subst hα
    rw [bigradα_eq_bot_of_neg L α (by omega)]
    exact bot_le
  · rintro x ⟨p, -, rfl⟩
    rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_neg (Ne.symm hα)]

variable (L) in
/-- **The weight shell**: a vector of charge `β` and weight `k < |β|²/2` is zero. -/
theorem eq_zero_of_charge_gradingG {β : L.carrier} {k : ℤ} (hk : k < halfNorm L β)
    {x : LatModuleGen L} (hx : x ∈ chargeSec L β) (hg : x ∈ gradingLatGen L k) : x = 0 := by
  obtain ⟨p, rfl⟩ := hx
  have h := gradingLatGen_le_ker_coordEαG L hk hg
  rw [LinearMap.mem_ker, mkEα_apply, coordEα_apply, if_pos rfl] at h
  rw [h, map_zero]

variable (hE hP) in
/-- Modes of a charged vacuum on a charged vacuum vanish beyond the pole order. -/
theorem mode_ch_ch_zeroG (x y : L.carrier) (n : ℕ) (h : 0 ≤ L.form x y + n) :
    mode ((WL L hE hP).Y (latChargeGen L x)) n (latChargeGen L y) = 0 := by
  have hY : (WL L hE hP).Y (latChargeGen L x) = Yeαvec L x := by
    have hw := YfullGen_word L hE hP [] x
    rwa [wordStateLatGen_nil, YwordLatGen_nil] at hw
  rw [hY, mode_apply, latChargeGen, Yeαvec_tmul, EEVec_vacuum, if_neg (by omega)]
  simp [latStateGen]

variable (hE hP) in
/-- Positive Cartan modes kill charged vacua. -/
theorem mode_hSt_posG (x y : L.carrier) (n : ℕ) (hn : 1 ≤ n) :
    mode ((WL L hE hP).Y (hSt L x)) n (latChargeGen L y) = 0 := by
  change (WL L hE hP).smul (hSt L x) n (latChargeGen L y) = 0
  rw [hSt_eq_sum, smul_sum_left]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [PreVertexAlgebra.smul_smul_left]
  change _ • mode ((WL L hE hP).Y (wordStateLatGen L [(0, a)] 0)) n (latChargeGen L y) = 0
  have hw : (WL L hE hP).Y (wordStateLatGen L [(0, a)] 0) = alphaLatGen L a := by
    change YfullGen L hE hP _ = _
    rw [YfullGen_word, BgA.YwordLatGen_singleton, genFieldLatGen_zero]
  rw [hw, mode_apply, alphaLatGen_apply, if_neg (by omega),
    add_zero, currentN_apply, latChargeGen, latStateGen, LinearMap.rTensor_tmul,
    oscN_vacuum _ _ _ _ (by omega), TensorProduct.zero_tmul, smul_zero]

theorem halfNorm_eq (hE : L.Even) (v : L.carrier) : 2 * halfNorm L v = L.form v v := by
  obtain ⟨k, hk⟩ := hE v
  rw [halfNorm, hk]
  omega

theorem form_comb (a b : ℤ) (x y : L.carrier) :
    L.form (a • x + b • y) (a • x + b • y) =
      a * a * L.form x x + a * b * (L.form x y + L.form y x) + b * b * L.form y y := by
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-! ## The realization data -/

/-- **Lattice realization data for a sector**: weight-one states with the sector bracket, each either a multiple
of a root vector `e^{rt i}` or a coroot `cv i (-1)𝟙`, and a root `θ` with the sign conditions of `ravFam`. -/
structure LatData (S : DeligneSectorData) (L : IntegralLattice) (hE : L.Even) (hP : L.PosDef) where
  X : Fin S.n → LatModuleGen L
  mem : ∀ i, X i ∈ (WL L hE hP).grading 1
  br : ∀ c d, (WL L hE hP).smul (X c) 0 (X d) = ∑ e, S.f c d e • X e
  cart : Fin S.n → Bool
  rt : Fin S.n → L.carrier
  sg : Fin S.n → ℂ
  cv : Fin S.n → L.carrier
  root : ∀ i, cart i = false → X i = sg i • latChargeGen L (rt i)
  coroot : ∀ i, cart i = true → X i = hSt L (cv i)
  θ : L.carrier
  raising : ∀ e, S.raising e → cart e = false ∧ 0 ≤ L.form (rt e) θ
  cartan : ∀ h, S.cartan h → cart h = true ∧ L.form (cv h) θ = S.thetaH h
  cartanN : ∀ h, S.cartanN h → cart h = true ∧ L.form (cv h) θ = -(S.thetaN h : ℤ)
  lowering : ∀ i, S.lowering i → cart i = false ∧ L.form (rt i) (rt i) = 2 ∧
    -(S.lowExp i : ℤ) ≤ L.form (rt i) θ
  fusion : ∀ x, S.fusion x → cart x = false ∧ (if x = S.c₀ then (-2 : ℤ) else -1) ≤ L.form (rt x) θ

namespace LatData

variable {S : DeligneSectorData} (D : LatData S L hE hP)

/-- The current module of the data. -/
abbrev ρ : CurrentModule S.f (LatModuleGen L) := latRepG S D.X D.mem D.br

/-- The realization vector `e^{Nθ}`. -/
abbrev vN (N : ℕ) : LatModuleGen L := latChargeGen L ((N : ℤ) • D.θ)

theorem op_apply (c : Fin S.n) (n : ℕ) (v : LatModuleGen L) :
    D.ρ.op c n v = mode ((WL L hE hP).Y (D.X c)) (n : ℤ) v := rfl

/-- A root letter with `⟨rt, Nθ⟩ + n ≥ 0` kills `e^{Nθ}`. -/
theorem op_root_zero {c : Fin S.n} (hc : D.cart c = false) (N n : ℕ)
    (h : 0 ≤ (N : ℤ) * L.form (D.rt c) D.θ + n) : D.ρ.op c n (D.vN N) = 0 := by
  rw [op_apply, D.root c hc, map_smul, mode_smul, LinearMap.smul_apply,
    mode_ch_ch_zeroG hE hP _ _ n (by rw [map_zsmul, smul_eq_mul]; exact h), smul_zero]

theorem op_cartan_pos {c : Fin S.n} (hc : D.cart c = true) (N n : ℕ) (hn : 1 ≤ n) :
    D.ρ.op c n (D.vN N) = 0 := by
  rw [op_apply, D.coroot c hc]
  exact mode_hSt_posG hE hP _ _ n hn

theorem op_cartan_zero {c : Fin S.n} (hc : D.cart c = true) (N : ℕ) :
    D.ρ.op c 0 (D.vN N) = (((N : ℤ) * L.form (D.cv c) D.θ : ℤ) : ℂ) • D.vN N := by
  rw [op_apply, D.coroot c hc]
  change (WL L hE hP).smul (hSt L (D.cv c)) 0 (latChargeGen L ((N : ℤ) • D.θ)) = _
  rw [show latChargeGen L ((N : ℤ) • D.θ) = latStateGen L (vacuumN _) ((N : ℤ) • D.θ) from rfl,
    smul_hSt_zero_latStateGen L hE hP, map_zsmul, smul_eq_mul, mul_comm]
  rfl

/-- The lowering iterate leaves the weight-`N²` shell. -/
theorem lowering_zero {i : Fin S.n} (hi : D.cart i = false) (hn : L.form (D.rt i) (D.rt i) = 2) (N m : ℕ)
    (hm : -(m : ℤ) ≤ L.form (D.rt i) D.θ) (hθ : L.form D.θ D.θ = 2) :
    (D.ρ.op i 0)^[N * m + 1] (D.vN N) = 0 := by
  have hc : D.X i ∈ chargeSec L (D.rt i) := by
    rw [D.root i hi]; exact Submodule.smul_mem _ _ (mem_chargeSec L _ _)
  have key : ∀ k : ℕ, (D.ρ.op i 0)^[k] (D.vN N) ∈ chargeSec L ((N : ℤ) • D.θ + (k : ℤ) • D.rt i) ∧
      (D.ρ.op i 0)^[k] (D.vN N) ∈ (WL L hE hP).grading ((N : ℤ) * N) := by
    intro k
    induction k with
    | zero =>
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_zero, id, Nat.cast_zero, zero_smul, add_zero]
          exact mem_chargeSec L _ _
        · have h := latChargeGen_mem_grading L ((N : ℤ) • D.θ)
          have h2 : halfNorm L ((N : ℤ) • D.θ) = (N : ℤ) * N := by
            have e := halfNorm_eq hE ((N : ℤ) • D.θ)
            have e2 := form_comb (N : ℤ) 0 D.θ D.θ
            simp only [zero_smul, add_zero, hθ] at e2
            rw [e2] at e
            linarith
          rw [h2] at h
          exact h
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        refine ⟨?_, ?_⟩
        · have := YfullGen_shiftsCharge L hE hP (D.rt i) hc _ (-((0 : ℕ) : ℤ) - 1) _ ih.1
          have hcs : D.rt i + ((N : ℤ) • D.θ + (k : ℤ) • D.rt i) =
              (N : ℤ) • D.θ + ((k + 1 : ℕ) : ℤ) • D.rt i := by
            push_cast; rw [add_smul, one_smul]; abel
          rw [← hcs]
          exact this
        · have h := (WL L hE hP).grading_mode (D.X i) (D.mem i) _ ih.2 0
          rwa [show (1 : ℤ) + (N * N) - 0 - 1 = N * N by ring] at h
  obtain ⟨h1, h2⟩ := key (N * m + 1)
  refine eq_zero_of_charge_gradingG L ?_ h1 h2
  set K : ℤ := ((N * m + 1 : ℕ) : ℤ) with hK
  set t : ℤ := L.form (D.rt i) D.θ with ht
  have e := halfNorm_eq hE ((N : ℤ) • D.θ + K • D.rt i)
  rw [form_comb, hθ, hn, form_comm' L D.θ (D.rt i)] at e
  have hK1 : 1 ≤ K := by rw [hK]; push_cast; nlinarith [Nat.zero_le (N * m)]
  have hKe : K = (N : ℤ) * m + 1 := by rw [hK]; push_cast; ring
  have hNt : 0 ≤ (N : ℤ) * (t + m) := mul_nonneg (Nat.cast_nonneg N) (by linarith)
  have hpos : 0 < K * ((N : ℤ) * t + K) := by
    apply mul_pos (by linarith)
    rw [hKe]; nlinarith
  nlinarith

/-- **`e^{Nθ}` satisfies the relations of `M_{N,0}`** (`ravFam S N 0`). -/
theorem sat (hθ : L.form D.θ D.θ = 2) (N : ℕ) : Sat S.f D.ρ (D.vN N) (ravFam S N 0) := by
  refine ⟨?_, ?_⟩
  · rintro t (⟨e, r, he, rfl⟩ | ⟨h, r, hc, hr, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨h, r, hc, hr, rfl⟩)
    · obtain ⟨h1, h2⟩ := D.raising e he
      exact D.op_root_zero h1 N r (by positivity)
    · exact D.op_cartan_pos (D.cartan h hc).1 N r hr
    · obtain ⟨h1, h2, h3⟩ := D.lowering i hi
      rw [← iterate_eq_wordOpG, show N + 0 = N by rfl]
      exact D.lowering_zero h1 h2 N _ h3 hθ
    · obtain ⟨h1, h2⟩ := D.fusion x hx
      change D.ρ.op x _ (D.vN N) = 0
      refine D.op_root_zero h1 N _ ?_
      by_cases hx0 : x = S.c₀
      · rw [if_pos hx0] at h2 ⊢; push_cast; nlinarith
      · rw [if_neg hx0] at h2 ⊢; push_cast; nlinarith
    · exact D.op_cartan_pos (D.cartanN h hc).1 N r hr
  · rintro q (⟨h, hc, rfl⟩ | ⟨h, hc, rfl⟩)
    · obtain ⟨h1, h2⟩ := D.cartan h hc
      rw [D.op_cartan_zero h1 N, h2]
      push_cast; ring_nf
    · obtain ⟨h1, h2⟩ := D.cartanN h hc
      rw [D.op_cartan_zero h1 N, h2]
      push_cast; ring_nf

/-- **The dimension half** (the remaining part of U7 on the lattice side): the degree pieces of the cyclic
submodule `U(𝔤[t]) e^{Nθ} ⊂ V_L` dominate `Dem N`. -/
def LatDim (Dem : ℕ → PowerSeries ℚ) (N : ℕ) : Prop :=
  ∀ M, PowerSeries.coeff M (Dem N) ≤ (Module.finrank ℂ (cycDeg D.ρ (D.vN N) M) : ℚ)

/-- **The lattice realization of `D(1, Nθ)`**: the relations half (`sat`, proved) plus the dimension half
(`LatDim`, named) give U7 in realization form. -/
theorem demazureRealizationG (hθ : L.form D.θ D.θ = 2) {Dem : ℕ → PowerSeries ℚ} {N : ℕ}
    (hdim : D.LatDim Dem N) : DemazureRealizationG S (ravFam S) Dem N :=
  ⟨LatModuleGen L, inferInstance, inferInstance, D.ρ, D.vN N, D.sat hθ N, hdim⟩

end LatData

end

end VOA.DeligneAudit.LatticeRealization

section AxiomAudit
#print axioms VOA.DeligneAudit.LatticeRealization.latRepG
#print axioms VOA.DeligneAudit.LatticeRealization.LatData.sat
#print axioms VOA.DeligneAudit.LatticeRealization.LatData.demazureRealizationG
end AxiomAudit
