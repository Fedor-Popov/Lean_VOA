/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbifoldIdentification

/-!
# Automorphisms and finite orbifolds of `V_{2m}`, `m ≥ 2`

Gannon–Rayhaun, Prop. C.4 / eq. (C.10) (Dong–Nagatomo): for `m ≥ 2`,
`Aut V_{2m} ≅ ℂ^× ⋊ ℤ₂`, and every finite subgroup is conjugate to a cyclic group `ℤ_n` of
charge rotations or to a dihedral group `D_n = ⟨ℤ_n, θ⟩`; hence every finite orbifold of
`V_{2m}` is in the list of Theorem 3.1.

## Main results
* `V2m_grading_one`: for `m ≥ 2` the weight-one space of `V_{2m}` is `ℂ h`, `h = α(−1)𝟙`
  (no `e^{kα}` has weight `1`; the Heisenberg weight-one space has rank one).
* `aut_hSt_eq_or_neg`: every automorphism sends `h ↦ ±h`. Proof: `g h = c h` with `c ≠ 0`; then
  `g e^α` is an `h₍₀₎`-eigenvector of eigenvalue `2m/c`, and the `h₍₀₎`-spectrum is `2mℤ`, so
  `1/c ∈ ℤ`; the same for `g⁻¹` gives `c ∈ ℤ`, so `c = ±1`.
* `aut_V2m_classify`: every `g ∈ Aut V_{2m}` (`m ≥ 2`) is `g_u` or `θ g_u` (`u ∈ ℂ^×`).
* `finite_subgroup_structure`: a finite subgroup of the normalizer `{g_u} ∪ {θ g_u}` (any `m`) is
  `(cycHom m hm n).range`, or is conjugated by some `g_w` onto `(dihHom m hm n).range`.
* `orbifold_conj_iso`: for any VOA `W`, `W^G ≅ W^{gGg⁻¹}`.
* `inCOneList_orbifold_V2m`: for `m ≥ 2`, every finite orbifold `V_{2m}^G` is in the list.
* `inCOneList_orbifold_V2_normalizer`, `inCOneList_orbifold_V2_torus`: the same for `m = 1`, for
  finite subgroups of the torus normalizer containing a nontrivial torus element, and for finite
  subgroups of the torus. The reflection subgroups `⟨θ g_v⟩ ≅ ℤ₂` (orbifold `V₂⁺ ≅ V₈`) are handled in
  `V2PlusV8.lean` (`inCOneList_orbifold_V2_normalizer_all`). Not covered here: the
  non-normalizer subgroups `A₄, S₄, A₅`.

## Status
`sorry`-free, no new axioms. Unconditional.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN MvPolynomial

/-! ## The weight-one space -/

/-- The weight-one Fock space is spanned by the single oscillators `a_a(−1)`. -/
theorem fock_weight_one_mem_span {r : ℕ} {p : FockN r} (hp : p ∈ gradingWN r 1) :
    p ∈ Submodule.span ℂ (Set.range fun a : Fin r => (X ((0 : ℕ), a) : FockN r)) := by
  classical
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hw : Finsupp.weight weightFnN d = 1 := hp (MvPolynomial.mem_support_iff.mp hd)
  have hd0 : d ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hd0
  have hi' : d i ≠ 0 := hi
  have hle : weightFnN i ≤ Finsupp.weight weightFnN d := Finsupp.le_weight_of_ne_zero' weightFnN hi'
  rw [hw, weightFnN_apply] at hle
  have hi0 : i.1 = 0 := by omega
  have hsingle : Finsupp.single i 1 ≤ d := by
    intro j
    rw [Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · exact Nat.zero_le _
  set e := d - Finsupp.single i 1 with he
  have hde : d = Finsupp.single i 1 + e := (add_tsub_cancel_of_le hsingle).symm
  have hwe : Finsupp.weight weightFnN e = 0 := by
    have h1 := hw
    have hs : Finsupp.weight weightFnN (Finsupp.single i 1) = 1 := by
      simp [Finsupp.weight_apply, Finsupp.sum_single_index, hi0]
    rw [hde, map_add, hs] at h1
    omega
  have he0 : e = 0 := by
    refine Finsupp.ext fun j => ?_
    by_contra hj
    have := Finsupp.le_weight_of_ne_zero' weightFnN hj
    rw [hwe, weightFnN_apply] at this
    omega
  rw [he0, add_zero] at hde
  have hi2 : i = ((0 : ℕ), i.2) := Prod.ext hi0 rfl
  rw [show monomial d (coeff d p) = coeff d p • (X i : FockN r) by
    rw [X, smul_monomial, smul_eq_mul, mul_one, ← hde]]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨i.2, ?_⟩)
  change X ((0 : ℕ), i.2) = X i
  rw [← hi2]

section Rank1

variable (m : ℕ) (hm : 1 ≤ m)

local notation "VV" => latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)

theorem latP_rootless (hm2 : 2 ≤ m) (v : ℤ) : (latP m).form v v ≠ 2 := by
  rw [latP_form]
  intro h
  have hv : v ≠ 0 := by rintro hv; rw [hv] at h; simp at h
  have h1 : 0 < v * v := mul_self_pos.mpr hv
  have h2 : (2 : ℤ) ≤ m := by exact_mod_cast hm2
  nlinarith

theorem heisSt_eq_mkEα (a : Fin (rank (latP m))) :
    heisSt (latP m) a = mkEα (latP m) 0 (X ((0 : ℕ), a)) := by
  rw [heisSt, wordStateLatGen_eq, wordStateN_cons, wordStateN_nil, mul_one]
  rfl

/-- **The weight-one space of `V_{2m}`, `m ≥ 2`, is `ℂ h`.** -/
theorem V2m_grading_one (hm2 : 2 ≤ m) {x : LatModuleGen (latP m)} (hx : x ∈ (VV).grading 1) :
    ∃ c : ℂ, x = c • hSt (latP m) (a1 m) := by
  have hx' : x ∈ gradingLatGen (latP m) 1 := hx
  have hle : gradingLatGen (latP m) 1 ≤ bigradα (latP m) (1, 0) := by
    refine iSup_le (fun α => ?_)
    rcases eq_or_ne α 0 with hα | hα
    · subst hα; rw [halfNorm_zero (latP m), sub_zero]
    · have hpos := halfNorm_pos (latP m) (latP_even m) (latP_posDef m hm) hα
      have h2 := two_halfNorm (latP m) (latP_even m) α
      have hne := latP_rootless m hm2 α
      rw [bigradα_eq_bot_of_neg (latP m) α (by omega : 1 - halfNorm (latP m) α < 0)]
      exact bot_le
  obtain ⟨q, hq, rfl⟩ := hle hx'
  rw [gradingZN_of_nonneg (by norm_num)] at hq
  have hq' := fock_weight_one_mem_span hq
  have hspan : (Submodule.span ℂ (Set.range fun a : Fin (rank (latP m)) => (X ((0 : ℕ), a) :
      FockN (rank (latP m))))).map (mkEα (latP m) 0) ≤ ℂ ∙ hSt (latP m) (a1 m) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [← heisSt_eq_mkEα]
    have h1 := heisSt_mem_span_hSt (latP m) (latP_posDef m hm) a
    have h2 : Submodule.span ℂ (Set.range (hSt (latP m))) ≤ ℂ ∙ hSt (latP m) (a1 m) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      rw [hSt_int m k]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    exact h2 h1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ⟨q, hq', rfl⟩)
  exact ⟨c, hc.symm⟩

theorem hSt_mem_grading_one : hSt (latP m) (a1 m) ∈ (VV).grading 1 := by
  have hb : hSt (latP m) (a1 m) ∈ bigradα (latP m) (1, 0) := by
    refine ⟨vSchur (latP m) (a1 m) 1, ?_, rfl⟩
    rw [gradingZN_of_nonneg (by norm_num)]
    exact Screen.vSchur_mem_gradingWN (latP m) (a1 m) 1
  have h := bigradα_le_gradingLatGen (latP m) 1 0 hb
  rwa [halfNorm_zero (latP m), add_zero] at h

/-! ## Automorphisms send `h ↦ ±h` -/

/-- The `h₍₀₎`-spectrum of `V_{2m}` is `2mℤ`. -/
theorem eig_hSt_int {y : LatModuleGen (latP m)} (hy : y ≠ 0) {lam : ℂ}
    (h : (VV).smul (hSt (latP m) (a1 m)) 0 y = lam • y) : ∃ k : ℤ, lam = 2 * (m : ℂ) * k := by
  by_contra hne
  push Not at hne
  apply hy
  apply eq_zero_of_coordEα (latP m)
  intro ν
  have h1 := coordEα_smul_hSt_zero (latP m) (latP_even m) (latP_posDef m hm) (a1 m) ν y
  rw [h, map_smul] at h1
  have h2 : (lam - (((latP m).form (a1 m) ν : ℤ) : ℂ)) • coordEα (latP m) ν y = 0 := by
    rw [sub_smul, h1, sub_self]
  refine (smul_eq_zero.mp h2).resolve_left ?_
  intro h0
  rw [sub_eq_zero, latP_form] at h0
  apply hne ν
  rw [h0]
  simp [a1]

theorem smul_hSt_zero_latChargeGen :
    (VV).smul (hSt (latP m) (a1 m)) 0 (latChargeGen (latP m) (a1 m))
      = (2 * (m : ℂ)) • latChargeGen (latP m) (a1 m) := by
  rw [latChargeGen, smul_hSt_zero_latStateGen, latP_form]
  congr 1
  push_cast [a1]
  ring

theorem aut_apply_ne_zero (g : Aut VV) {x : LatModuleGen (latP m)} (hx : x ≠ 0) : g x ≠ 0 := by
  intro h
  apply hx
  have := congrArg g.toLinearEquiv.symm h
  simpa using this

/-- If `g h = c h`, then `1/c ∈ ℤ`. -/
theorem inv_int_of_aut (g : Aut VV) {c : ℂ} (hc : c ≠ 0)
    (hg : g (hSt (latP m) (a1 m)) = c • hSt (latP m) (a1 m)) : ∃ k : ℤ, c⁻¹ = k := by
  set e := latChargeGen (latP m) (a1 m)
  have hy : g e ≠ 0 := aut_apply_ne_zero m hm g (latChargeGen_ne_zero m (a1 m))
  have h1 : c • (VV).smul (hSt (latP m) (a1 m)) 0 (g e) = (2 * (m : ℂ)) • g e := by
    have h0 : (VV).smul (c • hSt (latP m) (a1 m)) 0 (g e) = (2 * (m : ℂ)) • g e := by
      rw [← hg, ← Aut.map_smul, smul_hSt_zero_latChargeGen m hm, Aut.map_smul_c]
    simpa only [PreVertexAlgebra.smul_smul_left] using h0
  have h2 : (VV).smul (hSt (latP m) (a1 m)) 0 (g e) = (c⁻¹ * (2 * (m : ℂ))) • g e := by
    rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨k, hk⟩ := eig_hSt_int m hm hy h2
  refine ⟨k, ?_⟩
  have hm0 : (2 * (m : ℂ)) ≠ 0 := by
    have : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    exact mul_ne_zero two_ne_zero this
  have := hk
  rw [mul_comm] at this
  exact mul_left_cancel₀ hm0 this

/-- **Every automorphism of `V_{2m}` (`m ≥ 2`) sends `h ↦ ±h`.** -/
theorem aut_hSt_eq_or_neg (hm2 : 2 ≤ m) (g : Aut VV) :
    g (hSt (latP m) (a1 m)) = hSt (latP m) (a1 m) ∨
      g (hSt (latP m) (a1 m)) = -hSt (latP m) (a1 m) := by
  set h := hSt (latP m) (a1 m)
  have hh0 : h ≠ 0 := hSt_a1_ne_zero m hm
  obtain ⟨c, hc⟩ := V2m_grading_one m hm hm2
    (LatGen.Aut.mem_grading (latP m) g (hSt_mem_grading_one m hm))
  obtain ⟨c', hc'⟩ := V2m_grading_one m hm hm2
    (LatGen.Aut.mem_grading (latP m) g⁻¹ (hSt_mem_grading_one m hm))
  have hcc : c * c' = 1 := by
    have h1 : g⁻¹ (g h) = h := g.toLinearEquiv.symm_apply_apply h
    rw [hc, Aut.map_smul_c, hc', smul_smul] at h1
    have h2 : (c * c' - 1) • h = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hh0)
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc
  have hc0' : c' ≠ 0 := right_ne_zero_of_mul_eq_one hcc
  obtain ⟨k, hk⟩ := inv_int_of_aut m hm g hc0 hc
  obtain ⟨k', hk'⟩ := inv_int_of_aut m hm g⁻¹ hc0' hc'
  have hkk : k * k' = 1 := by
    have : ((k * k' : ℤ) : ℂ) = 1 := by
      push_cast
      rw [← hk, ← hk', ← mul_inv, hcc, inv_one]
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hkk with h1 | h1
  · left
    rw [hc, show c = 1 by rw [← inv_inv c, hk, h1]; simp, one_smul]
  · right
    rw [hc, show c = -1 by rw [← inv_inv c, hk, h1]; simp, neg_one_smul]

/-- **`Aut V_{2m} = {g_u} ⊔ {θ g_u}`** for `m ≥ 2` (Gannon–Rayhaun (C.10), Dong–Nagatomo):
`Aut V_{2m} ≅ ℂ^× ⋊ ℤ₂`. -/
theorem aut_V2m_classify (hm2 : 2 ≤ m) (g : Aut VV) :
    (∃ u : ℂˣ, g = charU m hm u) ∨ (∃ u : ℂˣ, g = thetaM m hm * charU m hm u) := by
  -- an automorphism fixing `h` is a torus element
  have key : ∀ φ : Aut VV, φ (hSt (latP m) (a1 m)) = hSt (latP m) (a1 m) →
      ∃ u : ℂˣ, φ = charU m hm u := by
    intro φ hφ
    set e := latChargeGen (latP m) (a1 m)
    have hc : φ e ∈ chargeSec (latP m) (a1 m) :=
      aut_mem_chargeSec m hm φ hφ (mem_chargeSec (latP m) (a1 m) _)
    have hg : φ e ∈ gradingLatGen (latP m) (halfNorm (latP m) (a1 m)) :=
      LatGen.Aut.mem_grading (latP m) φ (latChargeGen_mem_grading (latP m) (a1 m))
    obtain ⟨c, hce⟩ := exists_smul_of_grading_of_charge (latP m) (a1 m) hg hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hce
      exact aut_apply_ne_zero m hm φ (latChargeGen_ne_zero m (a1 m)) hce
    refine ⟨Units.mk0 c hc0, aut_ext_of_agree m hm _ _ ?_ ?_⟩
    · rw [hφ, charU_hSt]
    · rw [hce, charU_latChargeGen]
      change _ = ((Units.mk0 c hc0 ^ (1 : ℤ) : ℂˣ) : ℂ) • e
      rw [zpow_one, Units.val_mk0]
  rcases aut_hSt_eq_or_neg m hm hm2 g with h | h
  · exact Or.inl (key g h)
  · right
    obtain ⟨u, hu⟩ := key (thetaM m hm * g) (by
      rw [Aut.mul_apply, h, thetaAut_apply, ← neg_one_smul ℂ, map_smul, thetaLat_hSt',
        neg_one_smul, neg_neg])
    refine ⟨u, ?_⟩
    rw [← hu, ← mul_assoc, thetaM_mul_self, one_mul]

end Rank1

/-! ## Finite subgroups of the torus normalizer -/

theorem mem_range_zmodToUnits_iff (n : ℕ) [NeZero n] (u : ℂˣ) :
    u ∈ (zmodToUnits n).range ↔ u ∈ rootsOfUnity n ℂ := by
  rw [← (zetaU_isPrimitiveRoot (n := n)).zpowers_eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact ((AddEquiv.toMultiplicativeLeft (zetaU_isPrimitiveRoot (n := n)).zmodEquivZPowers) z).2
  · intro hu
    refine ⟨(AddEquiv.toMultiplicativeLeft
      (zetaU_isPrimitiveRoot (n := n)).zmodEquivZPowers).symm ⟨u, hu⟩, ?_⟩
    simp [zmodToUnits]

section Normalizer

variable (m : ℕ) (hm : 1 ≤ m)

local notation "VV" => latticeVOAGen (latP m) (latP_even m) (latP_posDef m hm)

theorem charU_mem_range_cycHom_iff (n : ℕ) [NeZero n] (u : ℂˣ) :
    charU m hm u ∈ (cycHom m hm n).range ↔ u ∈ rootsOfUnity n ℂ := by
  rw [← mem_range_zmodToUnits_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, charU_injective m hm hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simp [cycHom, hz]⟩

/-- `G` lies in the normalizer `{g_u} ⊔ {θ g_u}` of the torus. By `aut_V2m_classify` this holds
for every subgroup when `m ≥ 2`. -/
def InNormalizer (G : Subgroup (Aut VV)) : Prop :=
  ∀ g ∈ G, (∃ u : ℂˣ, g = charU m hm u) ∨ (∃ u : ℂˣ, g = thetaM m hm * charU m hm u)

/-- The torus part of a finite subgroup is the group of `n`-th roots of unity. -/
theorem torus_part (G : Subgroup (Aut VV)) [Finite G] :
    ∃ n : ℕ, ∃ _ : NeZero n, ∀ u : ℂˣ, charU m hm u ∈ G ↔ u ∈ rootsOfUnity n ℂ := by
  set H := G.comap (charU m hm)
  haveI : Finite H := Finite.of_injective (fun x : H => (⟨charU m hm x, x.2⟩ : G))
    (fun a b h => Subtype.ext (charU_injective m hm (congrArg Subtype.val h)))
  haveI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  refine ⟨Nat.card H, inferInstance, fun u => ?_⟩
  have hle : H ≤ rootsOfUnity (Nat.card H) ℂ := by
    intro x hx
    rw [mem_rootsOfUnity]
    have := pow_card_eq_one' (x := (⟨x, hx⟩ : H))
    exact congrArg Subtype.val this
  have heq : H = rootsOfUnity (Nat.card H) ℂ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_eq_fintype_card, Complex.card_rootsOfUnity])
  rw [← heq]
  rfl

theorem charU_mul_thetaM (w : ℂˣ) : charU m hm w * thetaM m hm = thetaM m hm * charU m hm w⁻¹ := by
  rw [thetaM_mul_charU, inv_inv]

theorem conj_charU (w u : ℂˣ) : MulAut.conj (charU m hm w) (charU m hm u) = charU m hm u := by
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, mul_comm w u, mul_inv_cancel_right]

theorem conj_thetaM_charU (w u : ℂˣ) :
    MulAut.conj (charU m hm w) (thetaM m hm * charU m hm u)
      = thetaM m hm * charU m hm (w⁻¹ * w⁻¹ * u) := by
  rw [MulAut.conj_apply, ← mul_assoc, charU_mul_thetaM, mul_assoc (thetaM m hm),
    mul_assoc (thetaM m hm), ← map_inv, ← map_mul, ← map_mul, mul_right_comm]

/-- **Finite subgroups of the torus normalizer** (any `m`): with `n = |G ∩ torus|`, either
`G = ℤ_n = (cycHom m hm n).range`, or `g_w G g_w⁻¹ = D_n = (dihHom m hm n).range` for some `w`. -/
theorem finite_subgroup_structure (G : Subgroup (Aut VV)) [Finite G] (hG : InNormalizer m hm G) :
    ∃ n : ℕ, ∃ _ : NeZero n, (∀ u : ℂˣ, charU m hm u ∈ G ↔ u ∈ rootsOfUnity n ℂ) ∧
      (G = (cycHom m hm n).range ∨
        ∃ w : ℂˣ, G.map (MulAut.conj (charU m hm w)).toMonoidHom = (dihHom m hm n).range) := by
  obtain ⟨n, hn, hT⟩ := torus_part m hm G
  refine ⟨n, hn, hT, ?_⟩
  -- torus elements of `G` are exactly the `cycHom` elements
  have hcyc : ∀ z : Multiplicative (ZMod n), cycHom m hm n z ∈ G := fun z =>
    (hT _).mpr ((mem_range_zmodToUnits_iff n _).mp ⟨z, rfl⟩)
  by_cases hθ : ∃ v : ℂˣ, thetaM m hm * charU m hm v ∈ G
  · right
    obtain ⟨v, hv⟩ := hθ
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (v : ℂ) two_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by rw [← hz]; ring)
    set w := Units.mk0 z hz0
    have hwv : w⁻¹ * w⁻¹ = v⁻¹ := by
      rw [← mul_inv]
      congr 1
      exact Units.ext (by simp [w, ← hz, sq])
    refine ⟨w, ?_⟩
    ext x
    constructor
    · intro hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
      rcases hG g hg with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · obtain ⟨z, hz⟩ := (charU_mem_range_cycHom_iff m hm n u).mpr ((hT u).mp hg)
        refine ⟨DihedralGroup.r (Multiplicative.toAdd z), ?_⟩
        change cycHom m hm n (Multiplicative.ofAdd (Multiplicative.toAdd z)) = _
        rw [ofAdd_toAdd, hz]
        exact (conj_charU m hm w u).symm
      · have hmem : charU m hm (v⁻¹ * u) ∈ G := by
          have := G.mul_mem (G.inv_mem hv) hg
          rwa [mul_inv_rev, ← map_inv, mul_assoc, ← mul_assoc (thetaM m hm)⁻¹, inv_mul_cancel,
            one_mul, ← map_mul] at this
        obtain ⟨z, hz⟩ := (charU_mem_range_cycHom_iff m hm n _).mpr ((hT _).mp hmem)
        refine ⟨DihedralGroup.sr (Multiplicative.toAdd z), ?_⟩
        change thetaM m hm * cycHom m hm n (Multiplicative.ofAdd (Multiplicative.toAdd z)) = _
        rw [ofAdd_toAdd, hz]
        change _ = MulAut.conj (charU m hm w) (thetaM m hm * charU m hm u)
        rw [conj_thetaM_charU, hwv]
    · rintro ⟨d, rfl⟩
      cases d with
      | r i =>
          refine Subgroup.mem_map.mpr ⟨cycHom m hm n (Multiplicative.ofAdd i), hcyc _, ?_⟩
          change MulAut.conj (charU m hm w) (charU m hm _) = _
          rw [conj_charU]
          rfl
      | sr i =>
          refine Subgroup.mem_map.mpr ⟨thetaM m hm * charU m hm v * cycHom m hm n
            (Multiplicative.ofAdd i), G.mul_mem hv (hcyc _), ?_⟩
          change MulAut.conj (charU m hm w)
            (thetaM m hm * charU m hm v * charU m hm (zmodToUnits n (Multiplicative.ofAdd i))) = _
          rw [mul_assoc, ← map_mul, conj_thetaM_charU, hwv, ← mul_assoc, inv_mul_cancel, one_mul]
          rfl
  · left
    push Not at hθ
    ext x
    constructor
    · intro hx
      rcases hG x hx with ⟨u, rfl⟩ | ⟨u, rfl⟩
      · exact (charU_mem_range_cycHom_iff m hm n u).mpr ((hT u).mp hx)
      · exact absurd hx (hθ u)
    · rintro ⟨z, rfl⟩
      exact hcyc z

end Normalizer

/-! ## Conjugation invariance of orbifolds -/

section Conj

variable {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

theorem orbifold_map_conj (g : Aut W) (G : Subgroup (Aut W)) :
    (orbifold G).carrier.map g.toLinearEquiv.toLinearMap
      = (orbifold (G.map (MulAut.conj g).toMonoidHom)).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ∀ k ∈ G, k x = x := hx
    intro k hk
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hk
    change (g * k' * g⁻¹) (g x) = g x
    rw [Aut.mul_apply, Aut.mul_apply, Aut.inv_apply, Aut.coe_toLinearEquiv,
      LinearEquiv.symm_apply_apply, hx' k' hk']
  · intro hy
    have hy' : ∀ k ∈ G.map (MulAut.conj g).toMonoidHom, k y = y := hy
    refine ⟨g⁻¹ y, fun k hk => ?_, ?_⟩
    · have h1 := hy' (g * k * g⁻¹) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
      rw [Aut.mul_apply, Aut.mul_apply] at h1
      have h2 := congrArg g.toLinearEquiv.symm h1
      rw [Aut.coe_toLinearEquiv, LinearEquiv.symm_apply_apply] at h2
      exact h2
    · change g (g⁻¹ y) = y
      rw [Aut.inv_apply, Aut.coe_toLinearEquiv]
      exact g.toLinearEquiv.apply_symm_apply y

/-- **Conjugate subgroups have isomorphic orbifolds**: `W^G ≅ W^{gGg⁻¹}`, via `x ↦ g x`. -/
theorem orbifold_conj_iso (g : Aut W) (G : Subgroup (Aut W)) :
    VOAIsomorphic (orbifoldVOA G) (orbifoldVOA (G.map (MulAut.conj g).toMonoidHom)) := by
  let f : (orbifold G).carrier ≃ₗ[ℂ] (orbifold (G.map (MulAut.conj g).toMonoidHom)).carrier :=
    (Submodule.equivMapOfInjective g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective
      (orbifold G).carrier).trans (LinearEquiv.ofEq _ _ (orbifold_map_conj g G))
  have hf : ∀ x, ((f x : (orbifold (G.map (MulAut.conj g).toMonoidHom)).carrier) : 𝒱)
      = g (x : 𝒱) := fun x => rfl
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [LinearEquiv.coe_toLinearMap, hf]
    exact g.map_vacuum
  · intro u k x
    apply Subtype.ext
    rw [LinearEquiv.coe_toLinearMap, hf]
    exact g.map_smul u k x
  · apply Subtype.ext
    rw [hf]
    exact g.map_omega

/-- `VOAIsomorphic` is transitive. -/
theorem voaIso_trans' {𝒲 𝒰 : Type*} [AddCommGroup 𝒲] [Module ℂ 𝒲] [AddCommGroup 𝒰] [Module ℂ 𝒰]
    {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲} {U : VertexOperatorAlgebra 𝒰}
    (h1 : VOAIsomorphic V T) (h2 : VOAIsomorphic T U) : VOAIsomorphic V U := by
  obtain ⟨e1, he1, hω1⟩ := h1
  obtain ⟨e2, he2, hω2⟩ := h2
  exact ⟨e1.trans e2, he2.comp he1, by simp [hω1, hω2]⟩

end Conj

/-! ## Finite orbifolds of `V_{2m}` are in the list -/

section Enumeration

/-- The orbifold of a finite subgroup of the torus normalizer of `V_{2m}`, when it is cyclic or
dihedral with `mn² ≥ 2`, is in the list. -/
theorem inCOneList_orbifold_of_normalizer (m : ℕ) (hm : 1 ≤ m) (G : Subgroup (Aut (V2m m hm)))
    [Finite G] (hN : InNormalizer m hm G)
    (h2 : ∀ n : ℕ, NeZero n → (∀ u : ℂˣ, charU m hm u ∈ G ↔ u ∈ rootsOfUnity n ℂ) →
      2 ≤ m * n ^ 2) :
    InCOneList (orbifoldVOA G) := by
  rw [inCOneList_iff_exists_label]
  obtain ⟨n, hn, hT, hG | ⟨w, hw⟩⟩ := @finite_subgroup_structure m hm G ‹Finite G› hN
  · subst hG
    exact ⟨_, hasCOneLabel_cyclic m hm n⟩
  · refine ⟨.plus (m * n ^ 2), one_le_mn2 m hm n, h2 n hn hT, ?_⟩
    have h := orbifold_conj_iso (charU m hm w) G
    rw [hw] at h
    exact voaIso_trans' h (orbifold_dihedral_iso m hm n)

/-- **Every finite orbifold of `V_{2m}`, `m ≥ 2`, is in the list** (the `m ≥ 2` half of the
enumeration input, Gannon–Rayhaun Prop. C.4): `V_{2m}^G ≅ V_{2mn²}` or `V_{2mn²}⁺`. -/
theorem inCOneList_orbifold_V2m (m : ℕ) (hm : 1 ≤ m) (hm2 : 2 ≤ m)
    (G : Subgroup (Aut (V2m m hm))) [Finite G] : InCOneList (orbifoldVOA G) := by
  refine inCOneList_orbifold_of_normalizer m hm G (fun g _ => aut_V2m_classify m hm hm2 g) ?_
  intro n hn _
  have h : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hn.ne)
  nlinarith

/-- For `m = 1`: a finite subgroup of the torus normalizer of `V₂` containing a nontrivial torus
element has its orbifold in the list. (The excluded case `G ≅ ℤ₂` generated by a reflection
`θ g_v` gives `V₂⁺ ≅ V₈`; see `V2PlusV8.lean`, `inCOneList_orbifold_V2_normalizer_all`.) -/
theorem inCOneList_orbifold_V2_normalizer (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G]
    (hN : InNormalizer 1 le_rfl G) (hnt : ∃ u : ℂˣ, u ≠ 1 ∧ charU 1 le_rfl u ∈ G) :
    InCOneList (orbifoldVOA G) := by
  refine inCOneList_orbifold_of_normalizer 1 le_rfl G hN ?_
  intro n hn hT
  obtain ⟨u, hu1, huG⟩ := hnt
  have hu := (hT u).mp huG
  have h2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by have := hn.ne; omega
    subst hn1
    rw [mem_rootsOfUnity, pow_one] at hu
    exact hu1 hu
  nlinarith

/-- For `m = 1`: every finite subgroup of the torus `{g_u}` of `Aut V₂` has orbifold `V_{2n²}`. -/
theorem inCOneList_orbifold_V2_torus (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G]
    (hG : ∀ g ∈ G, ∃ u : ℂˣ, g = charU 1 le_rfl u) : InCOneList (orbifoldVOA G) := by
  rw [inCOneList_iff_exists_label]
  obtain ⟨n, hn, hT, hG' | ⟨w, hw⟩⟩ :=
    @finite_subgroup_structure 1 le_rfl G ‹Finite G› (fun g hg => Or.inl (hG g hg))
  · subst hG'
    exact ⟨_, hasCOneLabel_cyclic 1 le_rfl n⟩
  · exfalso
    have hθ : thetaM 1 le_rfl ∈ G.map (MulAut.conj (charU 1 le_rfl w)).toMonoidHom := by
      rw [hw]
      refine ⟨DihedralGroup.sr 0, ?_⟩
      change thetaM 1 le_rfl * cycHom 1 le_rfl n (Multiplicative.ofAdd 0) = _
      rw [ofAdd_zero, map_one, mul_one]
    obtain ⟨g, hg, hgθ⟩ := Subgroup.mem_map.mp hθ
    obtain ⟨u, rfl⟩ := hG g hg
    change MulAut.conj (charU 1 le_rfl w) (charU 1 le_rfl u) = _ at hgθ
    rw [conj_charU] at hgθ
    apply thetaM_ne_charU 1 le_rfl u⁻¹
    rw [← hgθ, ← map_mul, mul_inv_cancel, map_one]

end Enumeration

end VOA.Classification.COne
