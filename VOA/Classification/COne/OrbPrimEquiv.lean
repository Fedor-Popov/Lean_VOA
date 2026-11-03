import VOA.Classification.COne.OrbPrimSix
import VOA.Classification.COne.AutV2Bridge

/-! # OrbPrim: equivariance of the polynomial model `T₂` under `Aut V₂`

* `T2_X`: `T₂(X_k)` is the `k`-th orthonormal basis vector `X, Y, Z` of `(V₂)₁`
  (`xyzL (Pi.single k 1)`).
* `substL A`: the substitution `X_k ↦ Σ_l (A e_k)_l X_l` for a linear map `A` of `ℂ³`;
  `phiE g = substL (autL g)` is an algebra automorphism, and `phi : tetra →* Aut ℂ[x,y,z]`.
* `T2_equivariant`: `g (T₂ F) = T₂ (phiE g F)` for EVERY automorphism `g` of `V₂` and every
  polynomial `F`. Degree one is the definition of `autL`; the induction step uses the Cartan
  product (`top_bin`), that `g` preserves primaries and descendants, and `Prim ∩ Desc = 0`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 VOA.IntegralLattice MvPolynomial OrbC2b

/-! ## The weight-one states -/

theorem fo_ePlus : fo (latChargeGen (latP 1) (a1 1)) =
    -(latticeCocycle (latP 1) (-a1 1) (a1 1)) • hSt (latP 1) (a1 1) := by
  have h := Qscr_latChargeGen_neg (latP 1) latP1_root'
  rw [neg_neg, hSt_neg] at h
  show Screen.Qscr (latP 1) (-a1 1) (latChargeGen (latP 1) (a1 1)) = _
  rw [h, smul_neg, neg_smul]

theorem fo_eMinus : fo (latChargeGen (latP 1) (-1 : ℤ)) = 0 := by
  rw [fo_eq]
  change V2v.smul (latChargeGen (latP 1) (-1 : ℤ)) 0
    (latStateGen (latP 1) (vacuumN _) (-1 : ℤ)) = 0
  rw [smul_chargeGen_state, EEVec_vacuum, latP_form, if_neg (by norm_num)]
  simp [latStateGen]

theorem fo_h : fo (hSt (latP 1) (a1 1)) = (2 : ℂ) • latChargeGen (latP 1) (-1 : ℤ) := by
  have h := V_EF (latChargeGen (latP 1) (-1 : ℤ))
  have he : eo (latChargeGen (latP 1) (-1 : ℤ)) = eps1 • hSt (latP 1) (a1 1) := by
    rw [eo_eq]; exact smul_e_f
  have hh : ho (latChargeGen (latP 1) (-1 : ℤ)) = (-2 : ℂ) • latChargeGen (latP 1) (-1 : ℤ) := by
    rw [VertexOperatorAlgebra.zeroMode_apply, show (1 : ℤ) - 1 = 0 by norm_num]
    have := smul_h_charge (-1)
    simpa using this
  rw [fo_eMinus, map_zero, zero_sub, he, map_smul, hh, smul_smul] at h
  apply smul_right_injective _ eps1_ne_zero
  change eps1 • fo (hSt (latP 1) (a1 1)) = eps1 • ((2 : ℂ) • latChargeGen (latP 1) (-1 : ℤ))
  rw [smul_smul, ← neg_neg (eps1 • fo (hSt (latP 1) (a1 1))), h, ← neg_smul]
  congr 1; ring

theorem cocycle_neg_one_one : latticeCocycle (latP 1) (-a1 1) (a1 1) = eps1 := by
  have hc := latticeCocycle_comm (latP 1) (latP_even 1) (a1 1) (-a1 1)
  have hp : (latP 1).form (a1 1) (-a1 1) = -2 := by rw [latP_form]; rfl
  rw [hp] at hc
  norm_num at hc
  have hs := latticeCocycle_sq (latP 1) (a1 1) (-a1 1)
  unfold eps1
  calc latticeCocycle (latP 1) (-a1 1) (a1 1)
      = (latticeCocycle (latP 1) (a1 1) (-a1 1) * latticeCocycle (latP 1) (a1 1) (-a1 1)) *
          latticeCocycle (latP 1) (-a1 1) (a1 1) := by rw [hs, one_mul]
    _ = latticeCocycle (latP 1) (a1 1) (-a1 1) := by rw [mul_assoc, hc, mul_one]

theorem wv10 : wv 1 0 = latChargeGen (latP 1) (a1 1) := wv_zero 1

theorem wv11 : wv 1 1 = (-(1 / 2 : ℂ) * eps1) • hSt (latP 1) (a1 1) := by
  rw [wv, cnk, vn, pow_one]
  change _ • fo (latChargeGen (latP 1) (a1 1)) = _
  rw [fo_ePlus, cocycle_neg_one_one, smul_smul]
  norm_num [Nat.factorial]

theorem wv12 : wv 1 2 = (-eps1) • latChargeGen (latP 1) (-1 : ℤ) := by
  rw [wv, cnk, vn, pow_two, Module.End.mul_apply]
  change _ • fo (fo (latChargeGen (latP 1) (a1 1))) = _
  rw [fo_ePlus, cocycle_neg_one_one, map_smul, fo_h, smul_smul, smul_smul]
  norm_num [Nat.factorial]
  congr 1; ring

theorem xyz_eq (a b c : ℂ) : xyz a b c = (a + Complex.I * b) • latChargeGen (latP 1) (a1 1) +
    c • hSt (latP 1) (a1 1) + (eps1 * a - Complex.I * eps1 * b) • latChargeGen (latP 1) (-1 : ℤ) := by
  rfl

theorem T2_X0 : T2 (X 0) = xyzL (Pi.single 0 1) := by
  rw [xyzL_apply, T2_apply, psi_X0, show (X 0 ^ 2 - X 1 ^ 2 : P2) =
      X 0 ^ 2 * X 1 ^ 0 - X 0 ^ 0 * X 1 ^ 2 by ring,
    map_sub, Tb_xy 2 0 1 rfl, Tb_xy 0 2 1 rfl, wv10, wv12, xyz_eq]
  simp only [Pi.single_eq_same, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
    Fin.isValue, Fin.reduceEq]
  module

theorem T2_X1 : T2 (X 1) = xyzL (Pi.single 1 1) := by
  rw [xyzL_apply, T2_apply, psi_X1, show (MvPolynomial.C Complex.I * (X 0 ^ 2 + X 1 ^ 2) : P2) =
      Complex.I • (X 0 ^ 2 * X 1 ^ 0 + X 0 ^ 0 * X 1 ^ 2) by rw [smul_eq_C_mul]; ring,
    map_smul, map_add, Tb_xy 2 0 1 rfl, Tb_xy 0 2 1 rfl, wv10, wv12, xyz_eq]
  simp only [Pi.single_eq_same, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
    Fin.isValue, Fin.reduceEq]
  module

theorem T2_X2 : T2 (X 2) = xyzL (Pi.single 2 1) := by
  rw [xyzL_apply, T2_apply, psi_X2, show (MvPolynomial.C (-2 * eps1) * (X 0 * X 1) : P2) =
      (-2 * eps1) • (X 0 ^ 1 * X 1 ^ 1) by rw [smul_eq_C_mul]; ring,
    map_smul, Tb_xy 1 1 1 rfl, wv11, xyz_eq, smul_smul]
  simp only [Pi.single_eq_same, ne_eq, not_false_eq_true, Pi.single_eq_of_ne,
    Fin.isValue, Fin.reduceEq]
  have : -2 * eps1 * (-(1 / 2) * eps1) = 1 := by linear_combination eps1_sq
  rw [this]
  module

/-- `T₂(X_k)` is the `k`-th orthonormal basis vector of `(V₂)₁`. -/
theorem T2_X (k : Fin 3) : T2 (X k) = xyzL (Pi.single k 1) := by
  fin_cases k
  · exact T2_X0
  · exact T2_X1
  · exact T2_X2

/-! ## Linear substitutions -/

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-- `lin v = Σ_k v_k X_k`. -/
def lin : (Fin 3 → ℂ) →ₗ[ℂ] P3 where
  toFun v := ∑ k, v k • (X k : P3)
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

theorem lin_single (k : Fin 3) : lin (Pi.single k 1) = X k := by
  simp only [lin, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single k (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul])
    (by simp), Pi.single_eq_same, one_smul]

theorem T2_lin (v : Fin 3 → ℂ) : T2 (lin v) = xyzL v := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin 3 → ℂ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [lin, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, T2_X]

/-- The substitution `X_k ↦ lin (A e_k)`. -/
def substL (A : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) : P3 →ₐ[ℂ] P3 :=
  aeval fun k => lin (A (Pi.single k 1))

theorem substL_X (A : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (k : Fin 3) :
    substL A (X k) = lin (A (Pi.single k 1)) := by
  rw [substL, aeval_X]

theorem substL_lin (A : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) (v : Fin 3 → ℂ) :
    substL A (lin v) = lin (A v) := by
  have hv : v = ∑ k, v k • (Pi.single k 1 : Fin 3 → ℂ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [lin, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, substL_X]

theorem substL_comp (A B : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) :
    (substL A).comp (substL B) = substL (A ∘ₗ B) :=
  MvPolynomial.algHom_ext fun k => by
    rw [AlgHom.comp_apply, substL_X, substL_X, substL_lin, LinearMap.comp_apply]

theorem substL_id : substL LinearMap.id = AlgHom.id ℂ P3 :=
  MvPolynomial.algHom_ext fun k => by rw [substL_X, LinearMap.id_apply, lin_single]; rfl

theorem lin_hom (v : Fin 3 → ℂ) : (lin v).IsHomogeneous 1 := by
  simp only [lin, LinearMap.coe_mk, AddHom.coe_mk]
  exact IsHomogeneous.sum _ _ _ fun k _ => by
    rw [smul_eq_C_mul]; simpa using (isHomogeneous_X ℂ k).C_mul (v k)

theorem substL_hom (A : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ)) {F : P3} {n : ℕ}
    (hF : F.IsHomogeneous n) : (substL A F).IsHomogeneous n := by
  have := hF.aeval (fun k => lin (A (Pi.single k 1))) (fun k => lin_hom _)
  rwa [one_mul] at this

/-- The action of an automorphism of `V₂` on polynomials. -/
def phiE (g : Aut V1) : P3 ≃ₐ[ℂ] P3 :=
  AlgEquiv.ofAlgHom (substL (autL g)) (substL (autL g⁻¹))
    (by rw [substL_comp, ← autL_mul, mul_inv_cancel, autL_one, substL_id])
    (by rw [substL_comp, ← autL_mul, inv_mul_cancel, autL_one, substL_id])

theorem phiE_apply (g : Aut V1) (F : P3) : phiE g F = substL (autL g) F := rfl

/-- `phiE` as a homomorphism on `Aut V₂`. -/
def phiHom : Aut V1 →* (P3 ≃ₐ[ℂ] P3) where
  toFun := phiE
  map_one' := AlgEquiv.ext fun F => by
    rw [phiE_apply, autL_one, substL_id]; rfl
  map_mul' g h := AlgEquiv.ext fun F => by
    rw [AlgEquiv.mul_apply, phiE_apply, phiE_apply, phiE_apply, autL_mul, ← substL_comp]; rfl

/-- `phi : tetra →* Aut ℂ[X₀,X₁,X₂]`. -/
def phi : tetra →* (P3 ≃ₐ[ℂ] P3) := phiHom.comp tetra.subtype

theorem phi_apply (g : tetra) (F : P3) : phi g F = phiE g.1 F := rfl

/-! ## Equivariance -/

theorem aut_lowerDesc (g : Aut V1) {N : ℤ} {x : Sp} (hx : x ∈ lowerDesc V2v N) :
    g x ∈ lowerDesc V2v N := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, y, hy, rfl⟩ := hz
    rw [show g (V2v.L (-(m : ℤ) - 1) y) = V2v.L (-(m : ℤ) - 1) (g y) from aut_comm_L g _ y]
    exact Submodule.subset_span ⟨m, _, Aut.map_grading g hy, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Aut.map_smul_c]; exact Submodule.smul_mem _ _ hx

theorem aut_prim (g : Aut V1) {N : ℤ} {x : Sp} (hx : x ∈ prim V2v N) : g x ∈ prim V2v N := by
  rw [mem_prim] at hx ⊢
  refine ⟨Aut.map_grading g hx.1, fun m => ?_⟩
  rw [show V2v.L ((m : ℤ) + 1) (g x) = g (V2v.L ((m : ℤ) + 1) x) from (aut_comm_L g _ x).symm,
    hx.2 m, map_zero]

theorem T2_equiv_X (g : Aut V1) (k : Fin 3) : g (T2 (X k)) = T2 (phiE g (X k)) := by
  rw [T2_X, phiE_apply, substL_X, T2_lin, ← xyzL_autL]

theorem T2_equiv_mul (g : Aut V1) {G H : P3} {s t : ℕ} (hGh : G.IsHomogeneous s)
    (hHh : H.IsHomogeneous t) (hG : g (T2 G) = T2 (phiE g G)) (hH : g (T2 H) = T2 (phiE g H)) :
    g (T2 (G * H)) = T2 (phiE g (G * H)) := by
  obtain ⟨U⟩ := v2VirUnitary_holds
  have hA := top_bin s t (mem_binDeg_of_hom (psi_hom hGh)) (mem_binDeg_of_hom (psi_hom hHh))
  have hB := top_bin s t (mem_binDeg_of_hom (psi_hom (substL_hom (autL g) hGh)))
    (mem_binDeg_of_hom (psi_hom (substL_hom (autL g) hHh)))
  rw [← map_mul] at hA hB
  change V2v.smul (T2 G) _ (T2 H) - _ • T2 (G * H) ∈ _ at hA
  change V2v.smul (T2 (phiE g G)) _ (T2 (phiE g H)) - _ • T2 (phiE g G * phiE g H) ∈ _ at hB
  have hA' := aut_lowerDesc g hA
  rw [map_sub, Aut.map_smul_c, show g (V2v.smul (T2 G) (topIdx s t) (T2 H)) =
      V2v.smul (g (T2 G)) (topIdx s t) (g (T2 H)) from g.map_smul' _ _ _, hG, hH] at hA'
  have hdiff : topSign s t • (T2 (phiE g (G * H)) - g (T2 (G * H))) ∈
      lowerDesc V2v (((s + t : ℕ) : ℤ) ^ 2) := by
    have := Submodule.sub_mem _ hA' hB
    rw [map_mul]
    convert this using 1
    rw [smul_sub]; abel
  have hd : T2 (phiE g (G * H)) - g (T2 (G * H)) ∈ lowerDesc V2v (((s + t : ℕ) : ℤ) ^ 2) := by
    have := Submodule.smul_mem _ (topSign s t)⁻¹ hdiff
    rwa [smul_smul, inv_mul_cancel₀ (topSign_ne_zero s t), one_smul] at this
  have hp : T2 (phiE g (G * H)) - g (T2 (G * H)) ∈ prim V2v (((s + t : ℕ) : ℤ) ^ 2) := by
    have h1 := T2_prim (substL_hom (autL g) (hGh.mul hHh))
    have h2 := aut_prim g (T2_prim (hGh.mul hHh))
    exact Submodule.sub_mem _ h1 h2
  have h0 : T2 (phiE g (G * H)) - g (T2 (G * H)) ∈ prim V2v (((s + t : ℕ) : ℤ) ^ 2) ⊓
      lowerDesc V2v (((s + t : ℕ) : ℤ) ^ 2) := ⟨hp, hd⟩
  rw [prim_inf_lowerDesc V2v U, Submodule.mem_bot, sub_eq_zero] at h0
  exact h0.symm

theorem T2_equiv_monomial (g : Aut V1) : ∀ n : ℕ, ∀ m : Fin 3 →₀ ℕ, m.degree = n →
    g (T2 (monomial m 1)) = T2 (phiE g (monomial m 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro m hm
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have hm0 : m = 0 := by
      ext i
      have := Finsupp.degree_eq_zero_iff m |>.mp hm
      simp [this]
    subst hm0
    rw [monomial_zero', C_1, map_one (phiE g), T2_vac]
    exact g.map_vacuum
  · obtain ⟨k, hk⟩ : ∃ k, m k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : m = 0 := Finsupp.ext hcon
      rw [this, map_zero] at hm
      omega
    set m' := m - Finsupp.single k 1 with hm'
    have hsplit : m = Finsupp.single k 1 + m' := by
      ext i
      simp only [hm', Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · simp
    have hdeg' : m'.degree = n - 1 := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single, hm] at this
      omega
    have hmono : (monomial m 1 : P3) = X k * monomial m' 1 := by
      rw [X, monomial_mul, one_mul, ← hsplit]
    rw [hmono]
    rcases Nat.eq_zero_or_pos (n - 1) with h1 | h1
    · have hm'0 : m' = 0 := by
        ext i
        have := Finsupp.degree_eq_zero_iff m' |>.mp (hdeg'.trans h1)
        simp [this]
      rw [hm'0, monomial_zero', C_1, mul_one]
      exact T2_equiv_X g k
    · exact T2_equiv_mul g (isHomogeneous_X ℂ k) (isHomogeneous_monomial _ hdeg')
        (T2_equiv_X g k) (ih (n - 1) (by omega) m' hdeg')

/-- **`T₂` is equivariant for every automorphism of `V₂`.** -/
theorem T2_equivariant (g : Aut V1) (F : P3) : g (T2 F) = T2 (phiE g F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [show monomial m a = a • (monomial m 1 : P3) by rw [smul_monomial, smul_eq_mul, mul_one],
      map_smul T2, Aut.map_smul_c, map_smul (phiE g), map_smul T2,
      T2_equiv_monomial g _ m rfl]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/-! ## The tetrahedral action on polynomials -/

open Equiv

/-- The four tetrahedral vectors in coordinates. -/
def tv (i : Fin 4) : Fin 3 → ℂ := ![ta i, tb i, tc i]

theorem tvec_eq (i : Fin 4) : tvec i = xyzL (tv i) := by
  rw [xyzL_apply]; rfl

theorem sgnC_even {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) : sgnC σ = 1 := by
  rw [sgnC, Equiv.Perm.mem_alternatingGroup.mp hσ]; simp

theorem autL_tv {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) (i : Fin 4) :
    autL (octHom σ) (tv i) = tv (σ i) := by
  apply xyzL_injective
  rw [xyzL_autL, ← tvec_eq, ← tvec_eq]
  have h := octFun_spec σ i
  rw [sgnC_even hσ, one_smul] at h
  exact h

/-- The linear forms `ℓ_i = t_i · X`. -/
def ell (i : Fin 4) : P3 := lin (tv i)

theorem phiE_ell {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) (i : Fin 4) :
    phiE (octHom σ) (ell i) = ell (σ i) := by
  rw [phiE_apply, ell, substL_lin, autL_tv hσ, ell]

theorem ell_eq (i : Fin 4) : ell i = ta i • X 0 + tb i • X 1 + tc i • X 2 := by
  simp only [ell, lin, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_three, tv]
  rfl

/-- Power sums of the `ℓ_i`. -/
def psum (k : ℕ) : P3 := ∑ i, ell i ^ k

theorem phiE_psum {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) (k : ℕ) :
    phiE (octHom σ) (psum k) = psum k := by
  rw [psum, map_sum]
  simp only [map_pow, phiE_ell hσ]
  exact Equiv.sum_comp σ (fun i => ell i ^ k)

theorem ell_explicit : (ell 0 = X 0 + X 1 + X 2) ∧ (ell 1 = X 0 - X 1 - X 2) ∧
    (ell 2 = -X 0 - X 1 + X 2) ∧ (ell 3 = -X 0 + X 1 - X 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [ell_eq] <;> simp [ta, tb, tc] <;> abel

theorem psum_two : psum 2 = (4 : ℂ) • r2 := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  rw [psum, Fin.sum_univ_four, h0, h1, h2, h3, r2, smul_eq_C_mul, map_ofNat]; ring

theorem psum_three : psum 3 = (24 : ℂ) • I3 := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  rw [psum, Fin.sum_univ_four, h0, h1, h2, h3, I3, smul_eq_C_mul, map_ofNat]; ring

theorem psum_four : psum 4 = (12 : ℂ) • r2 ^ 2 - (8 : ℂ) • I4 := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  rw [psum, Fin.sum_univ_four, h0, h1, h2, h3, r2, I4, smul_eq_C_mul, smul_eq_C_mul, map_ofNat,
    map_ofNat]; ring

/-- The Vandermonde determinant of the `ℓ_i`. -/
def vdm : P3 := (Matrix.vandermonde ell).det

theorem phiE_vdm {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) :
    phiE (octHom σ) vdm = vdm := by
  have h1 : (phiE (octHom σ) : P3 →ₐ[ℂ] P3).mapMatrix (Matrix.vandermonde ell) =
      (Matrix.vandermonde ell).submatrix σ id := by
    ext i j
    simp [Matrix.vandermonde_apply, phiE_ell hσ]
  have h2 := AlgHom.map_det (phiE (octHom σ) : P3 →ₐ[ℂ] P3) (Matrix.vandermonde ell)
  rw [h1, Matrix.det_permute, Equiv.Perm.mem_alternatingGroup.mp hσ] at h2
  simpa [vdm] using h2

theorem vdm_eq : vdm = (64 : ℂ) • I6 := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  have i0 : Finset.Ioi (0 : Fin 4) = {1, 2, 3} := by decide
  have i1 : Finset.Ioi (1 : Fin 4) = {2, 3} := by decide
  have i2 : Finset.Ioi (2 : Fin 4) = {3} := by decide
  have i3 : Finset.Ioi (3 : Fin 4) = ∅ := by decide
  rw [vdm, Matrix.det_vandermonde, Fin.prod_univ_four, i0, i1, i2, i3]
  simp only [Finset.prod_insert (show (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) by decide),
    Finset.prod_insert (show (2 : Fin 4) ∉ ({3} : Finset (Fin 4)) by decide),
    Finset.prod_singleton, Finset.prod_empty, mul_one]
  rw [h0, h1, h2, h3, I6, smul_eq_C_mul, map_ofNat]
  ring

theorem fix_gen {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) :
    Algebra.adjoin ℂ a4Gens ≤
      AlgHom.equalizer (phiE (octHom σ) : P3 →ₐ[ℂ] P3) (AlgHom.id ℂ P3) := by
  apply Algebra.adjoin_le
  intro F hF
  simp only [a4Gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hF
  change phiE (octHom σ) F = F
  rcases hF with rfl | rfl | rfl | rfl
  · have : r2 = (1 / 4 : ℂ) • psum 2 := by rw [psum_two, smul_smul]; norm_num
    rw [this, map_smul, phiE_psum hσ]
  · have : I3 = (1 / 24 : ℂ) • psum 3 := by rw [psum_three, smul_smul]; norm_num
    rw [this, map_smul, phiE_psum hσ]
  · have hr : phiE (octHom σ) r2 = r2 := by
      have : r2 = (1 / 4 : ℂ) • psum 2 := by rw [psum_two, smul_smul]; norm_num
      rw [this, map_smul, phiE_psum hσ]
    have : I4 = (1 / 8 : ℂ) • ((12 : ℂ) • r2 ^ 2 - psum 4) := by
      rw [psum_four, smul_sub, smul_sub, smul_smul, smul_smul]; norm_num
    rw [this, map_smul, map_sub, map_smul, map_pow, hr, phiE_psum hσ]
  · have : I6 = (1 / 64 : ℂ) • vdm := by rw [vdm_eq, smul_smul]; norm_num
    rw [this, map_smul, phiE_vdm hσ]

theorem phiE_fix {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) {F : P3}
    (hF : IsA4Inv F) : phiE (octHom σ) F = F :=
  fix_gen hσ (mem_adjoin_of_isA4Inv hF)

/-- `X_k = lin e_k` with `e_k = (t₀ + t_{p k})/2`. -/
def pk : Fin 3 → Fin 4 := ![1, 3, 2]

theorem single_eq_tv (k : Fin 3) :
    (Pi.single k 1 : Fin 3 → ℂ) = (1 / 2 : ℂ) • (tv 0 + tv (pk k)) := by
  ext i
  fin_cases k <;> fin_cases i <;> simp [tv, pk, ta, tb, tc] <;> norm_num

theorem phiE_X {σ : Perm (Fin 4)} (hσ : σ ∈ alternatingGroup (Fin 4)) (k : Fin 3) :
    phiE (octHom σ) (X k) = (1 / 2 : ℂ) • (ell (σ 0) + ell (σ (pk k))) := by
  rw [← lin_single, single_eq_tv, map_smul, map_add, ← ell, ← ell, map_smul, map_add,
    phiE_ell hσ, phiE_ell hσ]

theorem halfX_even : OrbC2b.halfX ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem halfY_even : OrbC2b.halfY ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem cycInv_even : OrbC2b.cycleThree⁻¹ ∈ alternatingGroup (Fin 4) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem phiE_halfX (F : P3) : phiE (octHom OrbC2b.halfX) F = s1 F := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  have h : (phiE (octHom OrbC2b.halfX) : P3 →ₐ[ℂ] P3) = s1 := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE _ (X k) = _
    rw [phiE_X halfX_even]
    fin_cases k
    · show (1 / 2 : ℂ) • (ell (OrbC2b.halfX 0) + ell (OrbC2b.halfX (pk 0))) = s1 (X 0)
      rw [show OrbC2b.halfX 0 = 1 by decide, show OrbC2b.halfX (pk 0) = 0 by decide, h1, h0]
      simp only [s1, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      module
    · show (1 / 2 : ℂ) • (ell (OrbC2b.halfX 0) + ell (OrbC2b.halfX (pk 1))) = s1 (X 1)
      rw [show OrbC2b.halfX 0 = 1 by decide, show OrbC2b.halfX (pk 1) = 2 by decide, h1, h2]
      simp only [s1, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← smul_eq_C_mul]
      module
    · show (1 / 2 : ℂ) • (ell (OrbC2b.halfX 0) + ell (OrbC2b.halfX (pk 2))) = s1 (X 2)
      rw [show OrbC2b.halfX 0 = 1 by decide, show OrbC2b.halfX (pk 2) = 3 by decide, h1, h3]
      simp only [s1, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← smul_eq_C_mul]
      module
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

theorem phiE_halfY (F : P3) : phiE (octHom OrbC2b.halfY) F = s2 F := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  have h : (phiE (octHom OrbC2b.halfY) : P3 →ₐ[ℂ] P3) = s2 := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE _ (X k) = _
    rw [phiE_X halfY_even]
    fin_cases k
    · show (1 / 2 : ℂ) • (ell (OrbC2b.halfY 0) + ell (OrbC2b.halfY (pk 0))) = s2 (X 0)
      rw [show OrbC2b.halfY 0 = 3 by decide, show OrbC2b.halfY (pk 0) = 2 by decide, h3, h2]
      simp only [s2, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← smul_eq_C_mul]
      module
    · show (1 / 2 : ℂ) • (ell (OrbC2b.halfY 0) + ell (OrbC2b.halfY (pk 1))) = s2 (X 1)
      rw [show OrbC2b.halfY 0 = 3 by decide, show OrbC2b.halfY (pk 1) = 0 by decide, h3, h0]
      simp only [s2, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      module
    · show (1 / 2 : ℂ) • (ell (OrbC2b.halfY 0) + ell (OrbC2b.halfY (pk 2))) = s2 (X 2)
      rw [show OrbC2b.halfY 0 = 3 by decide, show OrbC2b.halfY (pk 2) = 1 by decide, h3, h1]
      simp only [s2, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      rw [← smul_eq_C_mul]
      module
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

theorem phiE_cycInv (F : P3) : phiE (octHom OrbC2b.cycleThree⁻¹) F = rename cyc F := by
  obtain ⟨h0, h1, h2, h3⟩ := ell_explicit
  have h : (phiE (octHom OrbC2b.cycleThree⁻¹) : P3 →ₐ[ℂ] P3) = rename cyc := by
    apply MvPolynomial.algHom_ext
    intro k
    change phiE _ (X k) = _
    rw [phiE_X cycInv_even, rename_X]
    fin_cases k
    · show (1 / 2 : ℂ) • (ell (OrbC2b.cycleThree⁻¹ 0) + ell (OrbC2b.cycleThree⁻¹ (pk 0))) = X 1
      rw [show OrbC2b.cycleThree⁻¹ 0 = 0 by decide,
        show OrbC2b.cycleThree⁻¹ (pk 0) = 3 by decide, h0, h3]
      module
    · show (1 / 2 : ℂ) • (ell (OrbC2b.cycleThree⁻¹ 0) + ell (OrbC2b.cycleThree⁻¹ (pk 1))) = X 2
      rw [show OrbC2b.cycleThree⁻¹ 0 = 0 by decide,
        show OrbC2b.cycleThree⁻¹ (pk 1) = 2 by decide, h0, h2]
      module
    · show (1 / 2 : ℂ) • (ell (OrbC2b.cycleThree⁻¹ 0) + ell (OrbC2b.cycleThree⁻¹ (pk 2))) = X 0
      rw [show OrbC2b.cycleThree⁻¹ 0 = 0 by decide,
        show OrbC2b.cycleThree⁻¹ (pk 2) = 1 by decide, h0, h1]
      module
  exact congrArg (fun φ : P3 →ₐ[ℂ] P3 => φ F) h

/-! ## The residual, discharged -/

theorem mem_tetra_iff (g : Aut (V2m 1 le_rfl)) :
    g ∈ tetra ↔ ∃ σ ∈ alternatingGroup (Fin 4), octHom σ = g := Subgroup.mem_map

/-- **The residual of the polynomial model holds.** -/
theorem t2Residual : T2Residual phi := by
  refine T2Residual.of_eqv (fun g F => ?_) (fun g F hF => ?_) ?_ ?_ ?_ (fun g F n hF => ?_)
  · rw [phi_apply]; exact T2_equivariant g.1 F
  · obtain ⟨σ, hσ, hg⟩ := (mem_tetra_iff g.1).mp g.2
    rw [phi_apply, ← hg]
    exact phiE_fix hσ hF
  · exact ⟨⟨octHom OrbC2b.halfX, (mem_tetra_iff _).mpr ⟨_, halfX_even, rfl⟩⟩,
      fun F => phiE_halfX F⟩
  · exact ⟨⟨octHom OrbC2b.halfY, (mem_tetra_iff _).mpr ⟨_, halfY_even, rfl⟩⟩,
      fun F => phiE_halfY F⟩
  · exact ⟨⟨octHom OrbC2b.cycleThree⁻¹, (mem_tetra_iff _).mpr ⟨_, cycInv_even, rfl⟩⟩,
      fun F => phiE_cycInv F⟩
  · rw [phi_apply, phiE_apply]; exact substL_hom _ hF

/-- **B2: `TetraPrimaryReduction` holds** (Dong--Jiang Lemma 4.2 for `V₂^{A₄}`, primary part). -/
theorem tetraPrimaryReduction_holds : TetraPrimaryReduction :=
  tetraPrimaryReduction_of_T2Residual t2Residual

/-- **`TetrahedralVirasoroSpan` holds.** -/
theorem tetrahedralVirasoroSpan_holds : OrbC2c.TetrahedralVirasoroSpan :=
  tetrahedralVirasoroSpan_of_primaryReduction tetraPrimaryReduction_holds

/-- `C₂` for `V₂^{A₄}`, conditional only on the corrected Dong--Jiang relations. -/
theorem tetra_c2Cofinite_of_relations (hr : OrbC2Fix.TetrahedralDongJiangRelationsCorrected) :
    C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_primaryReduction tetraPrimaryReduction_holds hr

end VOA.Classification.COne.OrbPrim
