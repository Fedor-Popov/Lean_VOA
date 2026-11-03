import VOA.Classification.COne.OrbIcoCoef

/-! # OrbIco: the primary reduction for the standard icosahedral orbifold `V₂^{ico}`

`icoPrimaryReduction_std : PrimaryC2Reduction (orbifoldVOA ico) {𝟙, X}`, `X = T(J₆)` of
weight `36`.

Ingredients:
* the binary invariant theory (`icoInvariantSpan`): modulo `r²`, invariants are spanned by the
  monomials `J₆ᵃ J₁₀ᵇ J₁₅ᶜ`;
* products of two monomials lie in `O₂ + lowerDesc` by the top channel (`T2_top`);
* `T(J₁₀)` (weight `100`) is eliminated by `X₍₋₂₉₎X` (`second_bin`, `μ ≠ 0`), and `T(J₁₅)`
  (weight `225`) by `X₍₋₉₀₎T(J₁₀)` (`first_bin`, `λ ≠ 0`); the degree-ten invariant is
  *defined* by the channel, `J₁₀ = Reynolds(psi⁻¹ B₂(f,f))`, and the binary forms of both channels
  are shown `ico`-invariant by the "VOA trick" `binary_inv_of_channel`: an automorphism fixes the
  state and preserves lower descendants, while `Prim ∩ lowerDesc = 0`;
* the coefficient computations `cf_H_zero_ne` (`J₁₀(1, i, 0) ≠ 0`) and `cf_tv1_ne`
  (the weight-225 channel does not vanish).
-/

set_option maxSynthPendingDepth 3
set_option linter.style.longLine false
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIco
open VOA VertexOperatorAlgebra OrbSpan VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice
  MvPolynomial Equiv OrbPrim OrbOcta OrbC2b OrbRat6 Complex

local notation "V1" => latticeVOAGen (latP 1) (latP_even 1) (latP_posDef 1 le_rfl)

/-! ## The VOA trick -/

/-- If an `ico`-fixed state of `V₂` agrees with `μ Tb(B)` modulo lower descendants, then `B` is
the binary image of `ico`-invariant data: every `g ∈ ico` sends any homogeneous preimage of `B`
to a preimage of `B`. -/
theorem binary_inv_of_channel {S : Sp} {B : P2} {d : ℕ} {μ : ℂ} (hμ : μ ≠ 0)
    (hB : B ∈ binDeg (2 * d)) (hS : ∀ g ∈ ico, g S = S)
    (hrel : S - μ • Tb B ∈ lowerDesc V2v ((d : ℤ) ^ 2)) :
    ∀ g ∈ ico, ∀ F : P3, F.IsHomogeneous d → psi F = B → psi (phiE g F) = B := by
  intro g hg F hFh hF
  obtain ⟨U⟩ := v2VirUnitary_holds
  have hg1 : g (Tb B) = Tb (psi (phiE g F)) := by
    rw [← hF, ← T2_apply, T2_equivariant, T2_apply]
  have h1 := aut_lowerDesc g hrel
  rw [map_sub, Aut.map_smul_c, hS g hg, hg1] at h1
  have h2 : μ • (Tb (psi (phiE g F) - B)) ∈ lowerDesc V2v ((d : ℤ) ^ 2) := by
    have := Submodule.sub_mem _ hrel h1
    rw [map_sub, smul_sub]
    convert this using 1
    abel
  have h3 : Tb (psi (phiE g F) - B) ∈ lowerDesc V2v ((d : ℤ) ^ 2) := by
    have := Submodule.smul_mem _ μ⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hμ, one_smul] at this
  have hmem : psi (phiE g F) - B ∈ binDeg (2 * d) :=
    Submodule.sub_mem _ (mem_binDeg_of_hom (psi_hom (by rw [phiE_apply]; exact substL_hom _ hFh)))
      hB
  have h4 : Tb (psi (phiE g F) - B) ∈ prim V2v ((d : ℤ) ^ 2) := Tb_prim_of_binDeg hmem
  have h5 : Tb (psi (phiE g F) - B) ∈ prim V2v ((d : ℤ) ^ 2) ⊓ lowerDesc V2v ((d : ℤ) ^ 2) :=
    ⟨h4, h3⟩
  rw [prim_inf_lowerDesc V2v U, Submodule.mem_bot] at h5
  exact sub_eq_zero.mp (Tb_inj hmem h5)

/-- Lift a binary form, invariant in the sense of `binary_inv_of_channel`, to an invariant. -/
theorem lift_invariant {B : P2} {d : ℕ} (hB : B ∈ binDeg (2 * d))
    (hinv : ∀ g ∈ ico, ∀ F : P3, F.IsHomogeneous d → psi F = B → psi (phiE g F) = B) :
    ∃ G : P3, IcoInv G ∧ G.IsHomogeneous d ∧ psi G = B := by
  obtain ⟨F, hFh, hF⟩ := psi_surj_hom (binDeg_hom hB)
  exact ⟨reyI F, icoInv_reyI F, reyI_hom hFh, psi_reyI fun g hg => hinv g hg F hFh hF⟩

/-! ## The states -/

/-- `X = T(J₆) = Tb f`, the weight-`36` primary. -/
theorem T2_J6 : T2 J6 = Tb fpoly := by rw [T2_apply, psi_J6]

theorem ico_fix_T2 {F : P3} (hF : IcoInv F) : ∀ g ∈ ico, g (T2 F) = T2 F :=
  fun g hg => by rw [T2_equivariant, hF g hg]

theorem ico_fix_smul {a b : Sp} (ha : ∀ g ∈ ico, g a = a) (hb : ∀ g ∈ ico, g b = b) (n : ℤ) :
    ∀ g ∈ ico, g (V2v.smul a n b) = V2v.smul a n b := fun g hg => by
  rw [show g (V2v.smul a n b) = V2v.smul (g a) n (g b) from g.map_smul' _ _ _, ha g hg, hb g hg]

/-- The weight-100 channel: `X₍₋₂₉₎X ≡ μ Tb(H)`. -/
theorem chan100 : V2v.smul (T2 J6) (-29) (T2 J6) - mu2 • Tb Hpoly ∈
    lowerDesc V2v (((10 : ℕ) : ℤ) ^ 2) := by
  rw [T2_J6, Hpoly]
  exact second_bin fpoly_mem fpoly_mem

theorem Hpoly_mem' : Hpoly ∈ binDeg (2 * 10) := Hpoly_mem

/-- The degree-ten invariant, defined by the weight-100 channel. -/
theorem exists_J10 : ∃ G : P3, IcoInv G ∧ G.IsHomogeneous 10 ∧ psi G = Hpoly :=
  lift_invariant Hpoly_mem' (binary_inv_of_channel mu2_ne_zero Hpoly_mem'
    (ico_fix_smul (ico_fix_T2 icoInv_J6) (ico_fix_T2 icoInv_J6) (-29))
    (by exact_mod_cast chan100))

def J10 : P3 := exists_J10.choose
theorem icoInv_J10 : IcoInv J10 := exists_J10.choose_spec.1
theorem J10_hom : J10.IsHomogeneous 10 := exists_J10.choose_spec.2.1
theorem psi_J10 : psi J10 = Hpoly := exists_J10.choose_spec.2.2

theorem eval_J10 : eval ![1, I, 0] J10 ≠ 0 := by
  rw [← pt_one_zero, ← eval_psi, psi_J10, eval_one_zero Hpoly_mem]
  exact cf_H_zero_ne

theorem T2_J10 : T2 J10 = Tb Hpoly := by rw [T2_apply, psi_J10]

/-- The weight-225 channel: `X₍₋₉₀₎Y ≡ λ Tb((f, H)₁)`. -/
theorem chan225 : V2v.smul (T2 J6) (firstIdx 6 10) (T2 J10) -
    lamF 6 10 • Tb (tv1 fpoly Hpoly) ∈ lowerDesc V2v (((6 + 10 - 1 : ℕ) : ℤ) ^ 2) := by
  rw [T2_J6, T2_J10]
  exact first_bin 6 10 (by norm_num) (by norm_num) fpoly_mem Hpoly_mem

theorem tv1_mem' : tv1 fpoly Hpoly ∈ binDeg (2 * 15) := tv1_mem fpoly_mem Hpoly_mem

theorem exists_G15 : ∃ G : P3, IcoInv G ∧ G.IsHomogeneous 15 ∧ psi G = tv1 fpoly Hpoly :=
  lift_invariant tv1_mem' (binary_inv_of_channel (lamF_ne_zero 6 10 (by norm_num) (by norm_num))
    tv1_mem' (ico_fix_smul (ico_fix_T2 icoInv_J6) (ico_fix_T2 icoInv_J10) _)
    (by exact_mod_cast chan225))

theorem monoSet_fifteen : monoSet J10 15 = {J15} := by
  ext F
  simp only [monoSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, c, h, rfl⟩
    obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 1 := by omega
    simp
  · rintro rfl
    exact ⟨0, 0, 1, rfl, by simp⟩

/-- `(f, H)₁ = κ psi J₁₅` with `κ ≠ 0`. -/
theorem tv1_eq_J15 : ∃ κ : ℂ, κ ≠ 0 ∧ tv1 fpoly Hpoly = κ • psi J15 := by
  obtain ⟨G, hG, hGh, hψ⟩ := exists_G15
  have h := icoInvariantSpan J10 icoInv_J10 J10_hom eval_J10 15 G hG hGh
  rw [monoSet_fifteen, Set.image_singleton] at h
  obtain ⟨κ, hκ⟩ := Submodule.mem_span_singleton.mp h
  refine ⟨κ, ?_, by rw [← hψ, hκ]⟩
  rintro rfl
  rw [zero_smul, hψ] at hκ
  apply cf_tv1_ne
  rw [← hκ, map_zero]


/-! ## The orbifold `V₂^{ico}` -/

abbrev Wi : VertexOperatorAlgebra (orbifold ico).carrier := orbifoldVOA ico

/-- The averaged model `ℂ[x,y,z] → V₂^{ico}`. -/
abbrev TavI : P3 →ₗ[ℂ] (orbifold ico).carrier := avgT ico T2

theorem T2_mem_ico {F : P3} (hF : IcoInv F) : T2 F ∈ (orbifold ico).carrier :=
  fun g hg => by rw [T2_equivariant, hF g hg]

theorem TavI_coe {F : P3} (hF : IcoInv F) : (TavI F).val = T2 F := by
  have := OrbC2.average_fixed ico ⟨T2 F, T2_mem_ico hF⟩
  simp only [TavI, avgT, LinearMap.comp_apply]
  exact congrArg Subtype.val this

theorem average_T2_ico (F : P3) : OrbC2.average ico (T2 F) = TavI (reyI F) := by
  apply Subtype.ext
  rw [TavI_coe (icoInv_reyI F), OrbC2.average_val, reyI, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun g _ => T2_equivariant g.1 F

theorem average_smul_T2_ico {A B : P3} (hA : IcoInv A) (hB : IcoInv B) (k : ℤ) :
    OrbC2.average ico ((V2m 1 le_rfl).smul (T2 A) k (T2 B)) = Wi.smul (TavI A) k (TavI B) := by
  have hmem : (V2m 1 le_rfl).smul (T2 A) k (T2 B) ∈ (orbifold ico).carrier :=
    (orbifold ico).smul_mem _ (T2_mem_ico hA) _ _ (T2_mem_ico hB)
  rw [show (V2m 1 le_rfl).smul (T2 A) k (T2 B) =
      ((⟨_, hmem⟩ : (orbifold ico).carrier) : LatModuleGen (latP 1)) from rfl,
    OrbC2.average_fixed]
  apply Subtype.ext
  change _ = (V2m 1 le_rfl).smul (TavI A).val k (TavI B).val
  rw [TavI_coe hA, TavI_coe hB]

theorem TavI_one : TavI 1 = Wi.vacuum := by
  apply Subtype.ext
  rw [TavI_coe icoInv_one, T2_vac]
  rfl

theorem TavI_of_inv {F : P3} (hF : IcoInv F) : OrbC2.average ico (T2 F) = TavI F := by
  rw [average_T2_ico, reyI_of_inv hF]

/-- The seed `X = T(J₆)` of weight `36`. -/
def Xico : (orbifold ico).carrier := TavI J6

theorem Xico_grading : Xico ∈ Wi.grading 36 := by
  have h := T2_grad J6_hom
  change (TavI J6).val ∈ (V2m 1 le_rfl).grading _ 
  rw [TavI_coe icoInv_J6]
  simpa using h

/-! ## The two channel eliminations in the orbifold -/

theorem mem_O2_low_of_rel {N : ℤ} {x o : (orbifold ico).carrier} {c : ℂ} (hc : c ≠ 0)
    (ho : o ∈ O₂ Wi) (h : o - c • x ∈ lowerDesc Wi N) :
    x ∈ O₂ Wi ⊔ lowerDesc Wi N := by
  have : x = c⁻¹ • o - c⁻¹ • (o - c • x) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]; abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ ho))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ h))

/-- `T(J₁₀)` is eliminated by `X₍₋₂₉₎X`. -/
theorem TavI_J10_mem : TavI J10 ∈ O₂ Wi ⊔ lowerDesc Wi (((10 : ℕ) : ℤ) ^ 2) := by
  have h := average_lowerDesc ico chan100
  rw [map_sub, map_smul, average_smul_T2_ico icoInv_J6 icoInv_J6, ← T2_J10,
    TavI_of_inv icoInv_J10] at h
  exact mem_O2_low_of_rel mu2_ne_zero (smul_le_neg_two_mem_O₂ Wi _ _ (by norm_num)) h

/-- `T(J₁₅)` is eliminated by `X₍₋₉₀₎T(J₁₀)`. -/
theorem TavI_J15_mem : TavI J15 ∈ O₂ Wi ⊔ lowerDesc Wi (((15 : ℕ) : ℤ) ^ 2) := by
  obtain ⟨κ, hκ, heq⟩ := tv1_eq_J15
  have h := average_lowerDesc ico chan225
  rw [heq, map_smul, ← T2_apply, smul_smul, map_sub, map_smul,
    average_smul_T2_ico icoInv_J6 icoInv_J10, TavI_of_inv icoInv_J15] at h
  exact mem_O2_low_of_rel (mul_ne_zero (lamF_ne_zero 6 10 (by norm_num) (by norm_num)) hκ)
    (smul_le_neg_two_mem_O₂ Wi _ _ (by simp [firstIdx])) h

/-! ## Products -/

theorem TavI_mul_mem {u v : P3} (hu : IcoInv u) (hv : IcoInv v) {s t : ℕ}
    (hus : u.IsHomogeneous s) (hvt : v.IsHomogeneous t) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TavI (u * v) ∈ O₂ Wi ⊔ lowerDesc Wi (((s + t : ℕ) : ℤ) ^ 2) := by
  obtain ⟨c, hc⟩ := T2_top u v s t hus hvt
  have hav := average_lowerDesc ico hc
  rw [map_sub, map_smul, average_smul_T2_ico hu hv, TavI_of_inv (hu.mul hv)] at hav
  have hO : Wi.smul (TavI u) (-((2 * s * t : ℕ) : ℤ) - 1) (TavI v) ∈ O₂ Wi := by
    apply smul_le_neg_two_mem_O₂
    have : 1 ≤ 2 * s * t := by nlinarith
    omega
  have key : TavI (u * v) = c • Wi.smul (TavI u) (-((2 * s * t : ℕ) : ℤ) - 1) (TavI v) +
      (TavI (u * v) - c • Wi.smul (TavI u) (-((2 * s * t : ℕ) : ℤ) - 1) (TavI v)) := by abel
  rw [key]
  exact Submodule.add_mem_sup (Submodule.smul_mem _ _ hO) hav

/-! ## The monomials -/

theorem mono_inv (a b c : ℕ) : IcoInv (J6 ^ a * J10 ^ b * J15 ^ c) :=
  ((icoInv_J6.pow a).mul (icoInv_J10.pow b)).mul (icoInv_J15.pow c)

theorem mono_hom (a b c : ℕ) : (J6 ^ a * J10 ^ b * J15 ^ c).IsHomogeneous (6 * a + 10 * b + 15 * c) := by
  have := ((J6_hom.pow a).mul (J10_hom.pow b)).mul (J15_hom.pow c)
  convert this using 1

/-- The target of the primary reduction. -/
abbrev tgt (N : ℤ) : Submodule ℂ (orbifold ico).carrier :=
  O₂ Wi ⊔ Submodule.span ℂ ({Wi.vacuum, Xico} : Set (orbifold ico).carrier) ⊔ lowerDesc Wi N

theorem O2_low_le_tgt {N : ℤ} {x : (orbifold ico).carrier} (h : x ∈ O₂ Wi ⊔ lowerDesc Wi N) :
    x ∈ tgt N := by
  exact sup_le_sup_right (le_sup_left : O₂ Wi ≤ O₂ Wi ⊔
    Submodule.span ℂ ({Wi.vacuum, Xico} : Set (orbifold ico).carrier)) (lowerDesc Wi N) h

theorem mono_mem (a b c : ℕ) :
    TavI (J6 ^ a * J10 ^ b * J15 ^ c) ∈ tgt (((6 * a + 10 * b + 15 * c : ℕ) : ℤ) ^ 2) := by
  -- the four atoms
  by_cases h0 : a + b + c = 0
  · obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ c = 0 := by omega
    simp only [pow_zero, mul_one, TavI_one]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  by_cases h1 : a + b + c = 1
  · rcases (show (a = 1 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1)
      by omega) with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · simp only [pow_one, pow_zero, mul_one]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span
        (by simp [Xico])))
    · simp only [pow_one, pow_zero, mul_one, one_mul]
      exact O2_low_le_tgt (by simpa using TavI_J10_mem)
    · simp only [pow_one, pow_zero, mul_one, one_mul]
      exact O2_low_le_tgt (by simpa using TavI_J15_mem)
  -- products
  apply O2_low_le_tgt
  by_cases ha : 1 ≤ a
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have hm := TavI_mul_mem icoInv_J6 (mono_inv a' b c) J6_hom (mono_hom a' b c) (by norm_num)
      (by omega)
    rw [show J6 ^ (a' + 1) * J10 ^ b * J15 ^ c = J6 * (J6 ^ a' * J10 ^ b * J15 ^ c) by ring]
    convert hm using 3
    push_cast; ring
  by_cases hb : 1 ≤ b
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hm := TavI_mul_mem icoInv_J10 (mono_inv a b' c) J10_hom (mono_hom a b' c) (by norm_num)
      (by omega)
    rw [show J6 ^ a * J10 ^ (b' + 1) * J15 ^ c = J10 * (J6 ^ a * J10 ^ b' * J15 ^ c) by ring]
    convert hm using 3
    push_cast; ring
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hm := TavI_mul_mem icoInv_J15 (mono_inv a b c') J15_hom (mono_hom a b c') (by norm_num)
    (by omega)
  rw [show J6 ^ a * J10 ^ b * J15 ^ (c' + 1) = J15 * (J6 ^ a * J10 ^ b * J15 ^ c') by ring]
  convert hm using 3
  push_cast; ring

/-! ## The primary reduction -/

theorem TavI_inv_mem {F : P3} {n : ℕ} (hF : IcoInv F) (hh : F.IsHomogeneous n) :
    TavI F ∈ tgt ((n : ℤ) ^ 2) := by
  have hs := icoInvariantSpan J10 icoInv_J10 J10_hom eval_J10 n F hF hh
  have hT : T2 F ∈ Submodule.span ℂ (T2 '' monoSet J10 n) := by
    have := Submodule.mem_map_of_mem (f := Tb) hs
    rw [Submodule.map_span, ← Set.image_comp] at this
    rwa [T2_apply]
  have hA := Submodule.mem_map_of_mem (f := OrbC2.average ico) hT
  rw [Submodule.map_span, ← Set.image_comp, TavI_of_inv hF] at hA
  refine (Submodule.span_le.mpr ?_) hA
  rintro _ ⟨m, ⟨a, b, c, hd, rfl⟩, rfl⟩
  simp only [Function.comp_apply, SetLike.mem_coe]
  rw [TavI_of_inv (mono_inv a b c), ← hd]
  exact mono_mem a b c

/-- **Primary reduction for the standard icosahedral orbifold `V₂^{ico}`.** -/
theorem icoPrimaryReduction_std :
    PrimaryC2Reduction Wi ({Wi.vacuum, Xico} : Set (orbifold ico).carrier) := by
  intro N p hp
  have hp' := v2_prim_span N (orb_prim_coe ico hp)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  have hpa : p = OrbC2.average ico a + OrbC2.average ico b := by
    rw [← map_add, hab, OrbC2.average_fixed]
  rw [hpa]
  refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (average_lowerDesc ico hb))
  have hmap := Submodule.mem_map_of_mem (f := OrbC2.average ico) ha
  rw [Submodule.map_span] at hmap
  refine (Submodule.span_le.mpr ?_) hmap
  rintro _ ⟨_, ⟨F, ⟨n, hn, hN⟩, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, average_T2_ico, ← hN]
  exact TavI_inv_mem (icoInv_reyI F) (reyI_hom hn)

end VOA.Classification.COne.OrbIco
