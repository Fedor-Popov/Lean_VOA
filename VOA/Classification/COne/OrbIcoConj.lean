import VOA.Classification.COne.OrbIcoTransport
import VOA.Classification.COne.OrbC2dExceptional

/-! # OrbIco: conjugacy of icosahedral subgroups of `Aut V₂`

`icosahedralConjugacy`: every subgroup `G ≤ Aut V₂` with `G ≅ A₅` is conjugate to the standard
`ico`.

Proof.
1. The point stabilizer `A₄ ≤ A₅` normalizes a Klein four group, so (`conjugate_into_octa_of_normal_klein`,
   `tetra_eq_of_le_octa`) after conjugation `G ⊇ tetra`.
2. In `A₅` the element `rotC ∈ tetra` of order three is inverted by an involution `σ ∈ G`
   (`A5_inverter`, decided), and `σ ∉ tetra` (`A4_no_inverter`).
3. `σ` is a half-turn: `σ v = 2 (u·v) u − v` with `u·u = 1` (`exists_conj_charU`).
   Traces of `σ k`, `k ∈ {rotX, rotY, rotZ, rotC}`, are `4uᵢ² − 1` and `2(u₀u₁ + u₁u₂ + u₂u₀)`;
   elements of `A₅` have order `1, 2, 3, 5`, with traces `3, −1, 0` or a root of `t² − t − 1`.
   This forces `u = ±½(1, gq, −gp)` up to permutation: `σ` is a half-turn of `ico` or of
   `ico' = rot2 · ico · rot2⁻¹`.
4. `G ⊓ ico` (or `G ⊓ ico'`) contains `tetra` and `σ ∉ tetra`, so it has order `60`.
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice MvPolynomial Equiv Equiv.Perm OrbPrim
  OrbOcta OrbC2b OrbC2d Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## Finite group facts -/

theorem A5_orders : ∀ x : alternatingGroup (Fin 5), x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  decide +kernel

theorem A5_inverter : ∀ x : alternatingGroup (Fin 5), x ^ 3 = 1 → x ≠ 1 →
    ∃ s : alternatingGroup (Fin 5), s ^ 2 = 1 ∧ s ≠ 1 ∧ s * x * s = x⁻¹ := by
  decide +kernel

theorem A4_no_inverter : ∀ s c : alternatingGroup (Fin 4), c ^ 3 = 1 → c ≠ 1 → s ^ 2 = 1 →
    s * c * s = c⁻¹ → s = 1 := by
  decide +kernel

/-- The permutations of `rotC` and `rotZ`. -/
def cP : Perm (Fin 4) := transposition * finRotate 4
def zP : Perm (Fin 4) := finRotate 4 * finRotate 4

theorem A4_words : ∀ s : alternatingGroup (Fin 4), ∃ a b d : Fin 3,
    (s : Perm (Fin 4)) = cP ^ (a : ℕ) * zP ^ (b : ℕ) * cP ^ (d : ℕ) := by
  decide +kernel

theorem octHom_rot4 : octHom (finRotate 4) = rot4 := (octFun_spec _).unique isOct_rot4

theorem octHom_cP : octHom cP = rotC := by
  rw [cP, map_mul, octHom_transposition, octHom_rot4]; rfl

theorem octHom_zP : octHom zP = rotZ := by
  rw [zP, map_mul, octHom_rot4]; rfl

theorem tetra_le_ico : tetra ≤ ico := by
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨a, b, d, h⟩ := A4_words ⟨s, hs⟩
  change octHom s ∈ ico
  rw [show s = cP ^ (a : ℕ) * zP ^ (b : ℕ) * cP ^ (d : ℕ) from h, map_mul, map_mul, map_pow,
    map_pow, map_pow, octHom_cP, octHom_zP]
  exact ico.mul_mem (ico.mul_mem (ico.pow_mem rotC_mem _) (ico.pow_mem rotZ_mem _))
    (ico.pow_mem rotC_mem _)

theorem nat_card_ico : Nat.card ico = 60 := by
  rw [← nat_card_A5]
  exact (Nat.card_congr (MonoidHom.ofInjective icoHom_injective).toEquiv).symm

theorem nat_card_tetra : Nat.card tetra = 12 := by
  rw [Nat.card_congr tetra_group.some.toEquiv, nat_card_alternatingGroup]
  simp [Nat.factorial]

/-- The second icosahedral group containing `tetra`. -/
def ico' : Subgroup (Aut V1) := ico.map (MulAut.conj rot2).toMonoidHom

theorem nat_card_ico' : Nat.card ico' = 60 := by
  rw [ico', ← nat_card_ico]
  exact (Nat.card_congr (ico.equivMapOfInjective _ (MulAut.conj rot2).injective).toEquiv).symm

theorem rot2_conj_tetra {x : Aut V1} (hx : x ∈ tetra) : rot2⁻¹ * x * rot2 ∈ tetra := by
  obtain ⟨s, hs, rfl⟩ := hx
  refine ⟨transposition⁻¹ * s * transposition, ?_, ?_⟩
  · have := (inferInstance : (alternatingGroup (Fin 4)).Normal).conj_mem s hs transposition⁻¹
    simpa using this
  · change (octHom (transposition⁻¹ * s * transposition) : Aut V1) = rot2⁻¹ * octHom s * rot2
    rw [map_mul, map_mul, map_inv, octHom_transposition]

theorem tetra_le_ico' : tetra ≤ ico' := by
  have key : ∀ x : Aut V1, x ∈ tetra → x ∈ ico' := by
    intro x hx
    refine ⟨rot2⁻¹ * x * rot2, tetra_le_ico (rot2_conj_tetra hx), ?_⟩
    change rot2 * (rot2⁻¹ * x * rot2) * rot2⁻¹ = x
    group
  exact key


/-! ## Linear algebra of `autL` -/

/-- The trace of `g` on `(V₂)₁`. -/
def trA (g : Aut V1) : ℂ := ∑ k, autL g (Pi.single k 1) k

theorem trA_eq (g : Aut V1) : trA g = Matrix.trace (rho g) := by
  simp only [trA, Matrix.trace, Matrix.diag, rho, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.toMatrix'_apply]

theorem trA_conj (φ g : Aut V1) : trA (φ⁻¹ * g * φ) = trA g := by
  rw [trA_eq, trA_eq, map_mul, map_mul, Matrix.trace_mul_comm, ← mul_assoc, ← map_mul,
    mul_inv_cancel, map_one, one_mul]

theorem autL_inv_apply (φ : Aut V1) (v : Fin 3 → ℂ) : autL φ⁻¹ (autL φ v) = v := by
  rw [← LinearMap.comp_apply, ← autL_mul, inv_mul_cancel, autL_one, LinearMap.id_apply]

theorem autL_dot (φ : Aut V1) (x y : Fin 3 → ℂ) : autL φ x ⬝ᵥ autL φ y = x ⬝ᵥ y := by
  rw [← rho_mulVec, ← rho_mulVec, rho_dot]

theorem autL_injective {g h : Aut V1} (hgh : ∀ v, autL g v = autL h v) : g = h := by
  apply rho_injective
  ext i j
  have := congrFun (hgh (Pi.single j 1)) i
  simpa [rho, LinearMap.toMatrix'_apply] using this

theorem unitI_sq : unitI * unitI = -1 := by
  ext; simp [unitI]

theorem rotZ_eq_charU : rotZ = charU 1 le_rfl (-1) := by
  rw [rotZ, rot4, ← map_mul, unitI_sq]

theorem autL_charU (w : ℂˣ) (v : Fin 3 → ℂ) : autL (charU 1 le_rfl w) v =
    ![((w : ℂ) * (v 0 + I * v 1) + (w : ℂ)⁻¹ * (v 0 - I * v 1)) / 2,
      ((w : ℂ) * (v 0 + I * v 1) - (w : ℂ)⁻¹ * (v 0 - I * v 1)) / (2 * I), v 2] := by
  apply xyzL_injective
  rw [xyzL_autL]
  simp only [xyzL_apply, xyz]
  rw [charU_vec3]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  congr 1
  · simp; field_simp; ring_nf
  · simp; field_simp; ring_nf

theorem trA_charU (w : ℂˣ) : trA (charU 1 le_rfl w) = (w : ℂ) + (w : ℂ)⁻¹ + 1 := by
  simp only [trA, autL_charU, Fin.sum_univ_three]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  simp
  field_simp
  ring_nf


/-! ## Traces of elements of finite order -/

theorem trA_of_pow (g : Aut V1) (p : ℕ) (hp0 : 0 < p) (hp : g ^ p = 1) (hg : g ≠ 1) :
    ∃ w : ℂˣ, w ^ p = 1 ∧ w ≠ 1 ∧ trA g = (w : ℂ) + (w : ℂ)⁻¹ + 1 := by
  obtain ⟨φ, u, hφ⟩ := exists_conj_charU g (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp0, hp⟩)
  have hgφ : g = φ⁻¹ * charU 1 le_rfl u * φ := by rw [← hφ]; group
  refine ⟨u, ?_, ?_, ?_⟩
  · apply charU_injective 1 le_rfl
    rw [map_pow, ← hφ, map_one]
    rw [show (φ * g * φ⁻¹) ^ p = φ * g ^ p * φ⁻¹ from by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply], hp]
    group
  · rintro rfl
    apply hg
    rw [hgφ, map_one]; group
  · rw [hgφ, trA_conj, trA_charU]

theorem trA_two (g : Aut V1) (hp : g ^ 2 = 1) (hg : g ≠ 1) : trA g = -1 := by
  obtain ⟨w, hw, hw1, ht⟩ := trA_of_pow g 2 (by norm_num) hp hg
  have hx : (w : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hx1 : (w : ℂ) ≠ 1 := fun h => hw1 (Units.ext h)
  have : (w : ℂ) = -1 := by
    rcases eq_one_or_neg_one_of_sq hx with h | h
    · exact absurd h hx1
    · exact h
  rw [ht, this]; norm_num

theorem trA_three (g : Aut V1) (hp : g ^ 3 = 1) (hg : g ≠ 1) : trA g = 0 := by
  obtain ⟨w, hw, hw1, ht⟩ := trA_of_pow g 3 (by norm_num) hp hg
  have hx : (w : ℂ) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hx1 : (w : ℂ) ≠ 1 := fun h => hw1 (Units.ext h)
  have hx0 : (w : ℂ) ≠ 0 := Units.ne_zero w
  have hq : (w : ℂ) ^ 2 + w + 1 = 0 := by
    have : ((w : ℂ) - 1) * ((w : ℂ) ^ 2 + w + 1) = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx1)
  rw [ht]
  field_simp
  linear_combination hq

theorem trA_five (g : Aut V1) (hp : g ^ 5 = 1) (hg : g ≠ 1) : trA g ^ 2 - trA g - 1 = 0 := by
  obtain ⟨w, hw, hw1, ht⟩ := trA_of_pow g 5 (by norm_num) hp hg
  have hx : (w : ℂ) ^ 5 = 1 := by rw [← Units.val_pow_eq_pow_val, hw, Units.val_one]
  have hx1 : (w : ℂ) ≠ 1 := fun h => hw1 (Units.ext h)
  have hx0 : (w : ℂ) ≠ 0 := Units.ne_zero w
  have hq : (w : ℂ) ^ 4 + (w : ℂ) ^ 3 + (w : ℂ) ^ 2 + w + 1 = 0 := by
    have : ((w : ℂ) - 1) * ((w : ℂ) ^ 4 + (w : ℂ) ^ 3 + (w : ℂ) ^ 2 + w + 1) = 0 := by
      linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx1)
  rw [ht]
  field_simp
  linear_combination (-1 - (w : ℂ)) * hx + (w : ℂ) ^ 2 * hq

/-! ## Involutions are half-turns -/

theorem halfTurn (σ : Aut V1) (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ u : Fin 3 → ℂ, u ⬝ᵥ u = 1 ∧ ∀ v, autL σ v = (2 * (u ⬝ᵥ v)) • u - v := by
  obtain ⟨φ, w, hφ⟩ := exists_conj_charU σ (isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num,
    by rw [pow_two, h2]⟩)
  have hw2 : w * w = 1 := by
    apply charU_injective 1 le_rfl
    rw [map_mul, ← hφ, map_one]
    rw [show φ * σ * φ⁻¹ * (φ * σ * φ⁻¹) = φ * (σ * σ) * φ⁻¹ by group, h2]
    group
  have hw : w = -1 := by
    have hx : (w : ℂ) ^ 2 = 1 := by
      rw [pow_two, ← Units.val_mul, hw2, Units.val_one]
    rcases eq_one_or_neg_one_of_sq hx with h | h
    · exfalso; apply h1
      have : w = 1 := Units.ext h
      rw [this, map_one] at hφ
      have : σ = φ⁻¹ * (φ * σ * φ⁻¹) * φ := by group
      rw [this, hφ]; group
    · exact Units.ext h
  have hσ : σ = φ⁻¹ * rotZ * φ := by
    rw [rotZ_eq_charU, ← hw, ← hφ]; group
  refine ⟨autL φ⁻¹ (Pi.single 2 1), ?_, fun v => ?_⟩
  · rw [autL_dot]; simp [dotProduct, Fin.sum_univ_three]
  · rw [hσ, autL_mul, autL_mul, LinearMap.comp_apply, LinearMap.comp_apply, autL_rotZ]
    set a := autL φ v with ha
    have hdec : (![-a 0, -a 1, a 2] : Fin 3 → ℂ) = (2 * a 2) • Pi.single 2 1 - a := by
      funext k; fin_cases k <;> simp <;> ring
    have hinv : autL φ⁻¹ a = v := by rw [ha, autL_inv_apply]
    have hkey : a 2 = autL φ⁻¹ (Pi.single 2 1) ⬝ᵥ v := by
      have h3 : autL φ (autL φ⁻¹ (Pi.single 2 1)) = Pi.single 2 1 := by
        rw [← LinearMap.comp_apply, ← autL_mul, mul_inv_cancel, autL_one, LinearMap.id_apply]
      rw [← autL_dot φ, h3, ← ha]
      simp [dotProduct, Fin.sum_univ_three]
    rw [hdec, map_sub, map_smul, hinv, hkey]


/-! ## Half-turns about explicit axes -/

/-- `γ rotZ γ⁻¹` is the half-turn about `γ e_z`. -/
theorem conj_halfTurn (γ : Aut V1) (v : Fin 3 → ℂ) :
    autL (γ * rotZ * γ⁻¹) v =
      (2 * (autL γ (Pi.single 2 1) ⬝ᵥ v)) • autL γ (Pi.single 2 1) - v := by
  rw [autL_mul, autL_mul, LinearMap.comp_apply, LinearMap.comp_apply, autL_rotZ]
  set a := autL γ⁻¹ v with ha
  have hdec : (![-a 0, -a 1, a 2] : Fin 3 → ℂ) = (2 * a 2) • Pi.single 2 1 - a := by
    funext k; fin_cases k <;> simp; ring
  have hinv : autL γ a = v := by
    rw [ha, ← LinearMap.comp_apply, ← autL_mul, mul_inv_cancel, autL_one, LinearMap.id_apply]
  have hkey : a 2 = autL γ (Pi.single 2 1) ⬝ᵥ v := by
    rw [← hinv, autL_dot]
    simp [dotProduct, Fin.sum_univ_three]
  rw [hdec, map_sub, map_smul, hinv, hkey]

theorem conj_axis_dot (γ : Aut V1) :
    autL γ (Pi.single 2 1) ⬝ᵥ autL γ (Pi.single 2 1) = 1 := by
  rw [autL_dot]; simp [dotProduct, Fin.sum_univ_three]

/-- Two half-turns with axes orthogonal to `(1,1,1)` and the same squared coordinates agree. -/
theorem halfTurn_eq {σ h : Aut V1} {u a : Fin 3 → ℂ}
    (hσ : ∀ v, autL σ v = (2 * (u ⬝ᵥ v)) • u - v) (hh : ∀ v, autL h v = (2 * (a ⬝ᵥ v)) • a - v)
    (hsu : u 0 + u 1 + u 2 = 0) (hsa : a 0 + a 1 + a 2 = 0) (h0 : u 0 ^ 2 = a 0 ^ 2)
    (h1 : u 1 ^ 2 = a 1 ^ 2) (h2 : u 2 ^ 2 = a 2 ^ 2) : σ = h := by
  have p01 : u 0 * u 1 = a 0 * a 1 := by
    linear_combination (1 / 2 : ℂ) * (h2 - h0 - h1) - (1 / 2 : ℂ) * (u 2 - u 0 - u 1) * hsu +
      (1 / 2 : ℂ) * (a 2 - a 0 - a 1) * hsa
  have p02 : u 0 * u 2 = a 0 * a 2 := by
    linear_combination (1 / 2 : ℂ) * (h1 - h0 - h2) - (1 / 2 : ℂ) * (u 1 - u 0 - u 2) * hsu +
      (1 / 2 : ℂ) * (a 1 - a 0 - a 2) * hsa
  have p12 : u 1 * u 2 = a 1 * a 2 := by
    linear_combination (1 / 2 : ℂ) * (h0 - h1 - h2) - (1 / 2 : ℂ) * (u 0 - u 1 - u 2) * hsu +
      (1 / 2 : ℂ) * (a 0 - a 1 - a 2) * hsa
  apply autL_injective
  intro v
  rw [hσ, hh]
  funext k
  fin_cases k
  · simp [dotProduct, Fin.sum_univ_three]
    linear_combination (2 * v 0) * h0 + (2 * v 1) * p01 + (2 * v 2) * p02
  · simp [dotProduct, Fin.sum_univ_three]
    linear_combination (2 * v 0) * p01 + (2 * v 1) * h1 + (2 * v 2) * p12
  · simp [dotProduct, Fin.sum_univ_three]
    linear_combination (2 * v 0) * p02 + (2 * v 1) * p12 + (2 * v 2) * h2


/-! ## The candidate half-turns -/

theorem ico_halfTurn (i : Fin 15) : ∃ h ∈ ico, ∃ c : ℂ, c ^ 2 = 1 ∧
    ∀ v, autL h v = (2 * ((c / 2) • b2 i ⬝ᵥ v)) • ((c / 2) • b2 i) - v := by
  obtain ⟨γ, hγ, c, hc, he⟩ := b2_reach i
  have hb0 : b2 0 = (2 : ℂ) • Pi.single 2 1 := by
    funext j; fin_cases j <;> simp [b2]
  have ha : autL γ (Pi.single 2 1) = (c / 2) • b2 i := by
    have : (2 : ℂ) • autL γ (Pi.single 2 1) = c • b2 i := by rw [← map_smul, ← hb0, he]
    rw [show (c / 2) • b2 i = (1 / 2 : ℂ) • (c • b2 i) by rw [smul_smul]; ring_nf, ← this,
      smul_smul]
    norm_num
  have hc2 : c ^ 2 = 1 := by
    have h1 := autL_dot γ (b2 0) (b2 0)
    rw [he, b2_dot_self] at h1
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, b2_dot_self] at h1
    linear_combination h1 / 4
  refine ⟨γ * rotZ * γ⁻¹, ico.mul_mem (ico.mul_mem hγ rotZ_mem) (ico.inv_mem hγ), c, hc2,
    fun v => ?_⟩
  rw [conj_halfTurn, ha]

theorem rot2_vec (a : Fin 3 → ℂ) : autL rot2 a = ![-a 0, a 2, a 1] := by
  apply xyzL_injective
  rw [xyzL_autL]
  simp only [xyzL_apply, rot2_xyz]
  simp

theorem ico'_halfTurn (i : Fin 15) : ∃ h ∈ ico', ∃ c : ℂ, c ^ 2 = 1 ∧
    ∀ v, autL h v = (2 * (autL rot2 ((c / 2) • b2 i) ⬝ᵥ v)) • autL rot2 ((c / 2) • b2 i) - v := by
  obtain ⟨h, hh, c, hc, haf⟩ := ico_halfTurn i
  refine ⟨rot2 * h * rot2⁻¹, ⟨h, hh, rfl⟩, c, hc, fun v => ?_⟩
  rw [autL_mul, autL_mul, LinearMap.comp_apply, LinearMap.comp_apply, haf]
  have hinv : autL rot2 (autL rot2⁻¹ v) = v := by
    rw [← LinearMap.comp_apply, ← autL_mul, mul_inv_cancel, autL_one, LinearMap.id_apply]
  have hdot : (c / 2) • b2 i ⬝ᵥ autL rot2⁻¹ v = autL rot2 ((c / 2) • b2 i) ⬝ᵥ v := by
    rw [← autL_dot rot2, hinv]
  rw [map_sub, map_smul, hinv, hdot]

/-! ## Traces of `σ k` -/

def Tset (t : ℂ) : Prop := t = 3 ∨ t = -1 ∨ t = 0 ∨ t ^ 2 - t - 1 = 0

theorem trA_one : trA 1 = 3 := by
  simp [trA, autL_one, Fin.sum_univ_three]

theorem tset_of_order (y : Aut V1) (h : y = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 5 = 1) :
    Tset (trA y) := by
  by_cases hy : y = 1
  · left; rw [hy, trA_one]
  rcases h with h | h | h | h
  · exact absurd h hy
  · right; left; exact trA_two y h hy
  · right; right; left; exact trA_three y h hy
  · right; right; right; exact trA_five y h hy

theorem t_cases {t : ℂ} (h : Tset t) : t = 3 ∨ t = -1 ∨ t = 0 ∨ t = gp ∨ t = 1 - gp := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · have : (t - gp) * (t - (1 - gp)) = 0 := by linear_combination h - gp_sq'
    rcases mul_eq_zero.mp this with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (sub_eq_zero.mp h'))))

/-- The half-turn about the `y`-axis. -/
def rotY : Aut V1 := rotZ * rotX

theorem autL_rotY (v : Fin 3 → ℂ) : autL rotY v = ![-v 0, v 1, -v 2] := by
  rw [rotY, autL_mul, LinearMap.comp_apply, autL_rotX, autL_rotZ]
  funext k; fin_cases k <;> simp

section Traces
variable {σ : Aut V1} {u : Fin 3 → ℂ} (hu : u ⬝ᵥ u = 1)
  (hσ : ∀ v, autL σ v = (2 * (u ⬝ᵥ v)) • u - v)
include hu hσ

theorem trA_sX : trA (σ * rotX) = 4 * u 0 ^ 2 - 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hu
  simp [trA, autL_mul, autL_rotX, hσ, dotProduct, Fin.sum_univ_three, Pi.single_apply]
  linear_combination (-2 : ℂ) * hu

theorem trA_sY : trA (σ * rotY) = 4 * u 1 ^ 2 - 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hu
  simp [trA, autL_mul, autL_rotY, hσ, dotProduct, Fin.sum_univ_three, Pi.single_apply]
  linear_combination (-2 : ℂ) * hu

theorem trA_sZ : trA (σ * rotZ) = 4 * u 2 ^ 2 - 1 := by
  simp only [dotProduct, Fin.sum_univ_three] at hu
  simp [trA, autL_mul, autL_rotZ, hσ, dotProduct, Fin.sum_univ_three, Pi.single_apply]
  linear_combination (-2 : ℂ) * hu

omit hu in
theorem trA_sC : trA (σ * rotC) = 2 * (u 0 * u 1 + u 1 * u 2 + u 2 * u 0) := by
  simp [trA, autL_mul, autL_rotC, hσ, dotProduct, Fin.sum_univ_three, Pi.single_apply]
  ring

end Traces


/-! ## Identifying `σ` -/

theorem sqrt5_bounds : 2.2 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.3 := by
  constructor
  · rw [show (2.2 : ℝ) = Real.sqrt (2.2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (2.3 : ℝ) = Real.sqrt (2.3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

theorem cand_ico {σ : Aut V1} {u : Fin 3 → ℂ} (i : Fin 15)
    (hσ : ∀ v, autL σ v = (2 * (u ⬝ᵥ v)) • u - v) (hs : u 0 + u 1 + u 2 = 0)
    (hb : b2 i 0 + b2 i 1 + b2 i 2 = 0) (h0 : u 0 ^ 2 = b2 i 0 ^ 2 / 4)
    (h1 : u 1 ^ 2 = b2 i 1 ^ 2 / 4) (h2 : u 2 ^ 2 = b2 i 2 ^ 2 / 4) : σ ∈ ico := by
  obtain ⟨h, hh, c, hc, haf⟩ := ico_halfTurn i
  have : σ = h := by
    refine halfTurn_eq hσ haf hs ?_ ?_ ?_ ?_
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination (c / 2) * hb
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination h0 - (b2 i 0 ^ 2 / 4) * hc
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination h1 - (b2 i 1 ^ 2 / 4) * hc
    · simp only [Pi.smul_apply, smul_eq_mul]; linear_combination h2 - (b2 i 2 ^ 2 / 4) * hc
  rw [this]; exact hh

theorem cand_ico' {σ : Aut V1} {u : Fin 3 → ℂ} (i : Fin 15)
    (hσ : ∀ v, autL σ v = (2 * (u ⬝ᵥ v)) • u - v) (hs : u 0 + u 1 + u 2 = 0)
    (hb : -b2 i 0 + b2 i 2 + b2 i 1 = 0) (h0 : u 0 ^ 2 = b2 i 0 ^ 2 / 4)
    (h1 : u 1 ^ 2 = b2 i 2 ^ 2 / 4) (h2 : u 2 ^ 2 = b2 i 1 ^ 2 / 4) : σ ∈ ico' := by
  obtain ⟨h, hh, c, hc, haf⟩ := ico'_halfTurn i
  have : σ = h := by
    refine halfTurn_eq hσ haf hs ?_ ?_ ?_ ?_ <;> rw [rot2_vec] <;>
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · linear_combination (c / 2) * hb
    · linear_combination h0 - (b2 i 0 ^ 2 / 4) * hc
    · linear_combination h1 - (b2 i 2 ^ 2 / 4) * hc
    · linear_combination h2 - (b2 i 1 ^ 2 / 4) * hc
  rw [this]; exact hh

theorem gq_sq' : gq ^ 2 = 2 - gp := by rw [gq_eq]; linear_combination gp_sq'

set_option maxHeartbeats 8000000 in
-- 125 trace patterns.
/-- The involution `σ` lies in `ico` or `ico'`. -/
theorem sigma_mem {σ : Aut V1} {u : Fin 3 → ℂ} (hu : u ⬝ᵥ u = 1)
    (hσ : ∀ v, autL σ v = (2 * (u ⬝ᵥ v)) • u - v) (hs : u 0 + u 1 + u 2 = 0)
    (h0 : Tset (4 * u 0 ^ 2 - 1)) (h1 : Tset (4 * u 1 ^ 2 - 1)) (h2 : Tset (4 * u 2 ^ 2 - 1)) :
    σ ∈ ico ∨ σ ∈ ico' := by
  have hu' : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    simp only [dotProduct, Fin.sum_univ_three] at hu; linear_combination hu
  have hsum : (4 * u 0 ^ 2 - 1) + (4 * u 1 ^ 2 - 1) + (4 * u 2 ^ 2 - 1) = 1 := by
    linear_combination 4 * hu'
  have hz : ∀ x : ℂ, 4 * x ^ 2 - 1 = -1 → x = 0 := fun x hx =>
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linear_combination hx / 4)
  have b12 : b2 12 = ![gp, -1, -gq] := rfl
  have b13 : b2 13 = ![-gq, gp, -1] := rfl
  have b14 : b2 14 = ![-1, -gq, gp] := rfl
  have b3 : b2 3 = ![gp, 1, gq] := rfl
  have b8 : b2 8 = ![1, -gq, gp] := rfl
  have b10 : b2 10 = ![gq, gp, -1] := rfl
  have bnd := sqrt5_bounds
  rcases t_cases h0 with e0 | e0 | e0 | e0 | e0 <;>
  rcases t_cases h1 with e1 | e1 | e1 | e1 | e1 <;>
  rcases t_cases h2 with e2 | e2 | e2 | e2 | e2 <;>
  first
    | (exfalso
       have hh := hsum
       rw [e0, e1, e2] at hh
       have := congrArg Complex.re hh
       simp [gp_re] at this <;> linarith [bnd.1, bnd.2])
    | (exfalso
       have z1 := hz _ e1; have z2 := hz _ e2
       have z0 : u 0 = 0 := by linear_combination hs - z1 - z2
       rw [z0, z1, z2] at hu'; norm_num at hu')
    | (exfalso
       have z0 := hz _ e0; have z2 := hz _ e2
       have z1 : u 1 = 0 := by linear_combination hs - z0 - z2
       rw [z0, z1, z2] at hu'; norm_num at hu')
    | (exfalso
       have z0 := hz _ e0; have z1 := hz _ e1
       have z2 : u 2 = 0 := by linear_combination hs - z0 - z1
       rw [z0, z1, z2] at hu'; norm_num at hu')
    | (left; refine cand_ico 12 hσ hs ?_ ?_ ?_ ?_ <;> rw [b12] <;> simp <;>
        first | linear_combination gq_eq | linear_combination (-1 : ℂ) * gq_eq |
          linear_combination e0 / 4 | linear_combination e1 / 4 | linear_combination e2 / 4 |
          linear_combination e0 / 4 - gp_sq' / 4 | linear_combination e1 / 4 - gp_sq' / 4 |
          linear_combination e2 / 4 - gp_sq' / 4 | linear_combination e0 / 4 - gq_sq' / 4 |
          linear_combination e1 / 4 - gq_sq' / 4 | linear_combination e2 / 4 - gq_sq' / 4)
    | (left; refine cand_ico 13 hσ hs ?_ ?_ ?_ ?_ <;> rw [b13] <;> simp <;>
        first | linear_combination gq_eq | linear_combination (-1 : ℂ) * gq_eq |
          linear_combination e0 / 4 | linear_combination e1 / 4 | linear_combination e2 / 4 |
          linear_combination e0 / 4 - gp_sq' / 4 | linear_combination e1 / 4 - gp_sq' / 4 |
          linear_combination e2 / 4 - gp_sq' / 4 | linear_combination e0 / 4 - gq_sq' / 4 |
          linear_combination e1 / 4 - gq_sq' / 4 | linear_combination e2 / 4 - gq_sq' / 4)
    | (left; refine cand_ico 14 hσ hs ?_ ?_ ?_ ?_ <;> rw [b14] <;> simp <;>
        first | linear_combination gq_eq | linear_combination (-1 : ℂ) * gq_eq |
          linear_combination e0 / 4 | linear_combination e1 / 4 | linear_combination e2 / 4 |
          linear_combination e0 / 4 - gp_sq' / 4 | linear_combination e1 / 4 - gp_sq' / 4 |
          linear_combination e2 / 4 - gp_sq' / 4 | linear_combination e0 / 4 - gq_sq' / 4 |
          linear_combination e1 / 4 - gq_sq' / 4 | linear_combination e2 / 4 - gq_sq' / 4)
    | (right; refine cand_ico' 3 hσ hs ?_ ?_ ?_ ?_ <;> rw [b3] <;> simp <;>
        first | linear_combination gq_eq | linear_combination (-1 : ℂ) * gq_eq |
          linear_combination e0 / 4 | linear_combination e1 / 4 | linear_combination e2 / 4 |
          linear_combination e0 / 4 - gp_sq' / 4 | linear_combination e1 / 4 - gp_sq' / 4 |
          linear_combination e2 / 4 - gp_sq' / 4 | linear_combination e0 / 4 - gq_sq' / 4 |
          linear_combination e1 / 4 - gq_sq' / 4 | linear_combination e2 / 4 - gq_sq' / 4)
    | (right; refine cand_ico' 8 hσ hs ?_ ?_ ?_ ?_ <;> rw [b8] <;> simp <;>
        first | linear_combination gq_eq | linear_combination (-1 : ℂ) * gq_eq |
          linear_combination e0 / 4 | linear_combination e1 / 4 | linear_combination e2 / 4 |
          linear_combination e0 / 4 - gp_sq' / 4 | linear_combination e1 / 4 - gp_sq' / 4 |
          linear_combination e2 / 4 - gp_sq' / 4 | linear_combination e0 / 4 - gq_sq' / 4 |
          linear_combination e1 / 4 - gq_sq' / 4 | linear_combination e2 / 4 - gq_sq' / 4)
    | (right; refine cand_ico' 10 hσ hs ?_ ?_ ?_ ?_ <;> rw [b10] <;> simp <;>
        first | linear_combination gq_eq | linear_combination (-1 : ℂ) * gq_eq |
          linear_combination e0 / 4 | linear_combination e1 / 4 | linear_combination e2 / 4 |
          linear_combination e0 / 4 - gp_sq' / 4 | linear_combination e1 / 4 - gp_sq' / 4 |
          linear_combination e2 / 4 - gp_sq' / 4 | linear_combination e0 / 4 - gq_sq' / 4 |
          linear_combination e1 / 4 - gq_sq' / 4 | linear_combination e2 / 4 - gq_sq' / 4)


/-! ## `A₄ ↪ A₅` and the first conjugation -/

/-- `Fin 4 ≃ ` the image of `Fin.castSucc` in `Fin 5`. -/
def castEquiv : Fin 4 ≃ Set.range (Fin.castSucc : Fin 4 → Fin 5) :=
  Equiv.ofInjective _ (Fin.castSucc_injective 4)

open Classical in
/-- The point stabilizer embedding `A₄ → A₅`. -/
def a4toA5 : alternatingGroup (Fin 4) →* alternatingGroup (Fin 5) :=
  ((extendDomainHom castEquiv).comp (alternatingGroup (Fin 4)).subtype).codRestrict _
    (fun x => by
      rw [mem_alternatingGroup]
      change Perm.sign ((x : Perm (Fin 4)).extendDomain castEquiv) = 1
      rw [sign_extendDomain]
      exact x.2)

theorem a4toA5_injective : Function.Injective a4toA5 := by
  intro x y h
  have := congrArg Subtype.val h
  exact Subtype.ext (extendDomainHom_injective castEquiv this)

theorem conj_to_tetra (G : Subgroup (Aut V1)) (e : G ≃* alternatingGroup (Fin 5)) :
    ∃ g : Aut V1, tetra ≤ G.map (MulAut.conj g).toMonoidHom := by
  let f : alternatingGroup (Fin 4) →* Aut V1 := G.subtype.comp (e.symm.toMonoidHom.comp a4toA5)
  have hf : Function.Injective f :=
    G.subtype_injective.comp (e.symm.injective.comp a4toA5_injective)
  obtain ⟨g, hg⟩ := conjugate_into_octa_of_normal_klein f hf kleinAlt kleinAlt_injective
    kleinAlt_normal
  have hiso : (f.range.map (MulAut.conj g).toMonoidHom) ≃* alternatingGroup (Fin 4) :=
    (f.range.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans
      (MonoidHom.ofInjective hf).symm
  have heq := tetra_eq_of_le_octa _ hiso hg
  refine ⟨g, ?_⟩
  rw [← heq]
  apply Subgroup.map_mono
  rintro _ ⟨x, rfl⟩
  exact (e.symm (a4toA5 x)).2

/-! ## The coordinate generators lie in `tetra` -/

theorem cP_even : cP ∈ alternatingGroup (Fin 4) := by rw [mem_alternatingGroup]; decide
theorem zP_even : zP ∈ alternatingGroup (Fin 4) := by rw [mem_alternatingGroup]; decide

theorem rotC_mem_tetra : rotC ∈ tetra := ⟨cP, cP_even, octHom_cP⟩
theorem rotZ_mem_tetra : rotZ ∈ tetra := ⟨zP, zP_even, octHom_zP⟩
theorem rotX_mem_tetra : rotX ∈ tetra :=
  tetra.mul_mem (tetra.mul_mem (tetra.mul_mem rotC_mem_tetra rotC_mem_tetra) rotZ_mem_tetra)
    rotC_mem_tetra
theorem rotY_mem_tetra : rotY ∈ tetra := tetra.mul_mem rotZ_mem_tetra rotX_mem_tetra

theorem rotC_ne_one : rotC ≠ 1 := by
  intro h
  have := congrArg (fun g => autL g (Pi.single 0 1) 2) h
  simp [autL_rotC, autL_one] at this

/-! ## Cardinality -/

theorem eq_of_tetra_le {G' K : Subgroup (Aut V1)} (hK : Nat.card K = 60) (hG : Nat.card G' = 60)
    (hT1 : tetra ≤ G') (hT2 : tetra ≤ K) {σ : Aut V1} (hσG : σ ∈ G') (hσK : σ ∈ K)
    (hσT : σ ∉ tetra) : G' = K := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Finite G' := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  set H := G' ⊓ K with hHdef
  have hfinH : Finite H :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right : H ≤ K))
  have hTH : tetra ≤ H := le_inf hT1 hT2
  have h12 : 12 ∣ Nat.card H := nat_card_tetra ▸ Subgroup.card_dvd_of_le hTH
  have h60 : Nat.card H ∣ 60 := hK ▸ Subgroup.card_dvd_of_le inf_le_right
  have hne : Nat.card H ≠ 12 := by
    intro h
    have := @Subgroup.eq_of_le_of_card_ge _ _ tetra H hfinH hTH
      (le_of_eq (h.trans nat_card_tetra.symm))
    exact hσT (this ▸ ⟨hσG, hσK⟩)
  have hH : Nat.card H = 60 := by
    obtain ⟨k, hk⟩ := h12
    have hpos : 0 < Nat.card H := Nat.pos_of_dvd_of_pos h60 (by norm_num)
    have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num) h60
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl <;> simp_all <;> omega
  have hHK : H = K := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hK, hH])
  have hHG : H = G' := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hG, hH])
  rw [← hHG, hHK]


/-! ## The conjugacy theorem -/

theorem rotC_cube' : rotC ^ 3 = 1 := by rw [pow_succ, pow_two, rotC_cube]

/-- **Every icosahedral subgroup of `Aut V₂` is conjugate to `ico`.** -/
theorem icosahedralConjugacy (G : Subgroup (Aut V1))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) :
    ∃ g : Aut V1, G.map (MulAut.conj g).toMonoidHom = ico := by
  obtain ⟨e⟩ := hG
  obtain ⟨g, hT⟩ := conj_to_tetra G e
  set G' := G.map (MulAut.conj g).toMonoidHom with hG'
  let e' : G' ≃* alternatingGroup (Fin 5) :=
    (G.equivMapOfInjective _ (MulAut.conj g).injective).symm.trans e
  have hcard : Nat.card G' = 60 := by
    rw [Nat.card_congr e'.toEquiv, nat_card_A5]
  have hC : rotC ∈ G' := hT rotC_mem_tetra
  have hX : rotX ∈ G' := hT rotX_mem_tetra
  have hY : rotY ∈ G' := hT rotY_mem_tetra
  have hZ : rotZ ∈ G' := hT rotZ_mem_tetra
  -- orders
  have hord : ∀ y ∈ G', y = 1 ∨ y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 5 = 1 := by
    intro y hy
    have h := A5_orders (e' ⟨y, hy⟩)
    have hinj : ∀ (k : ℕ), (e' ⟨y, hy⟩) ^ k = 1 → y ^ k = 1 := by
      intro k hk
      have : (⟨y, hy⟩ : G') ^ k = 1 := by
        apply e'.injective; rw [map_pow, hk, map_one]
      exact congrArg Subtype.val this |>.trans rfl |> fun h' => by simpa using h'
    rcases h with h | h | h | h
    · left
      have : (⟨y, hy⟩ : G') = 1 := by apply e'.injective; rw [h, map_one]
      exact congrArg Subtype.val this
    · exact Or.inr (Or.inl (hinj 2 h))
    · exact Or.inr (Or.inr (Or.inl (hinj 3 h)))
    · exact Or.inr (Or.inr (Or.inr (hinj 5 h)))
  -- the inverting involution
  have hx3 : (e' ⟨rotC, hC⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨rotC, hC⟩ : G') ^ 3 = 1 := Subtype.ext (by simpa using rotC_cube')
    rw [this, map_one]
  have hx1 : e' ⟨rotC, hC⟩ ≠ 1 := by
    intro h
    apply rotC_ne_one
    have : (⟨rotC, hC⟩ : G') = 1 := by apply e'.injective; rw [h, map_one]
    exact congrArg Subtype.val this
  obtain ⟨s, hs2, hs1, hsx⟩ := A5_inverter _ hx3 hx1
  set σ' : G' := e'.symm s with hσ'
  have hσ2 : (σ' : Aut V1) * σ' = 1 := by
    have : σ' * σ' = 1 := by
      apply e'.injective; rw [map_mul, hσ', MulEquiv.apply_symm_apply, ← pow_two, hs2, map_one]
    exact congrArg Subtype.val this
  have hσ1 : (σ' : Aut V1) ≠ 1 := by
    intro h
    apply hs1
    have : σ' = 1 := Subtype.ext h
    rw [← MulEquiv.apply_symm_apply e' s, ← hσ', this, map_one]
  have hσC : (σ' : Aut V1) * rotC * σ' = rotC⁻¹ := by
    have : σ' * ⟨rotC, hC⟩ * σ' = (⟨rotC, hC⟩ : G')⁻¹ := by
      apply e'.injective
      rw [map_mul, map_mul, hσ', MulEquiv.apply_symm_apply, hsx, map_inv]
    exact congrArg Subtype.val this
  set σ : Aut V1 := (σ' : Aut V1) with hσdef
  have hσG : σ ∈ G' := σ'.2
  -- `σ ∉ tetra`
  have hσT : σ ∉ tetra := by
    intro hσt
    obtain ⟨τ⟩ := tetra_group
    have h := A4_no_inverter (τ ⟨σ, hσt⟩) (τ ⟨rotC, rotC_mem_tetra⟩)
      (by rw [← map_pow]; rw [show (⟨rotC, rotC_mem_tetra⟩ : tetra) ^ 3 = 1 from
        Subtype.ext (by simpa using rotC_cube'), map_one])
      (by intro h; apply rotC_ne_one
          have : (⟨rotC, rotC_mem_tetra⟩ : tetra) = 1 := by
            apply τ.injective; rw [h, map_one]
          exact congrArg Subtype.val this)
      (by rw [← map_pow, show (⟨σ, hσt⟩ : tetra) ^ 2 = 1 from
        Subtype.ext (by simpa [pow_two] using hσ2), map_one])
      (by rw [← map_mul, ← map_mul, ← map_inv]; congr 1; exact Subtype.ext hσC)
    apply hσ1
    have : (⟨σ, hσt⟩ : tetra) = 1 := by apply τ.injective; rw [h, map_one]
    exact congrArg Subtype.val this
  -- the half-turn data
  obtain ⟨u, hu, hσu⟩ := halfTurn σ hσ2 hσ1
  have hσCinv : (σ * rotC) ^ 2 = 1 := by
    rw [pow_two, show σ * rotC * (σ * rotC) = (σ * rotC * σ) * rotC by group, hσC,
      inv_mul_cancel]
  have hσCne : σ * rotC ≠ 1 := by
    intro h
    have h' : σ = rotC⁻¹ := eq_inv_of_mul_eq_one_left h
    have h2 : rotC⁻¹ * rotC⁻¹ = 1 := h' ▸ hσ2
    apply rotC_ne_one
    have h2' : rotC * rotC = 1 := by
      have := congrArg (·⁻¹) h2
      simpa [mul_inv_rev] using this
    calc rotC = (rotC * rotC * rotC) * (rotC * rotC)⁻¹ := by group
      _ = 1 := by rw [rotC_cube, h2', inv_one, one_mul]
  have hsum : u 0 + u 1 + u 2 = 0 := by
    have h1 := trA_two (σ * rotC) hσCinv hσCne
    rw [trA_sC hσu] at h1
    have hu' : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
      simp only [dotProduct, Fin.sum_univ_three] at hu; linear_combination hu
    have : (u 0 + u 1 + u 2) ^ 2 = 0 := by linear_combination hu' + h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have t0 := tset_of_order _ (hord _ (G'.mul_mem hσG hX))
  have t1 := tset_of_order _ (hord _ (G'.mul_mem hσG hY))
  have t2 := tset_of_order _ (hord _ (G'.mul_mem hσG hZ))
  rw [trA_sX hu hσu] at t0
  rw [trA_sY hu hσu] at t1
  rw [trA_sZ hu hσu] at t2
  rcases sigma_mem hu hσu hsum t0 t1 t2 with hm | hm
  · exact ⟨g, eq_of_tetra_le nat_card_ico hcard hT tetra_le_ico hσG hm hσT⟩
  · have hG'eq := eq_of_tetra_le nat_card_ico' hcard hT tetra_le_ico' hσG hm hσT
    refine ⟨rot2⁻¹ * g, ?_⟩
    have hcomp : (MulAut.conj (rot2⁻¹ * g)).toMonoidHom =
        (MulAut.conj rot2⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, ← Subgroup.map_map, ← hG', hG'eq, ico', Subgroup.map_map]
    have hid : (MulAut.conj rot2⁻¹).toMonoidHom.comp (MulAut.conj rot2).toMonoidHom =
        MonoidHom.id _ := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hid, Subgroup.map_id]

end VOA.Classification.COne.OrbIco
