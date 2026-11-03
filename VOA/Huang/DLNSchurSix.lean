import VOA.Huang.DLNSchurCriterion

/-! # A central-extension proof for the six-element dihedral group -/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl
open scoped commutatorElement

private theorem conjugate_commutator {E : Type*} [Group E] (a b : E)
    (ha : a ^ 2 ∈ Subgroup.center E) :
    a * ⁅a, b⁆ * a⁻¹ = ⁅a, b⁆⁻¹ := by
  calc
    a * ⁅a, b⁆ * a⁻¹ = (a ^ 2 * b * (a ^ 2)⁻¹) * (a * b⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def, pow_two]
      group
    _ = b * (a * b⁻¹ * a⁻¹) := by
      rw [← Subgroup.mem_center_iff.mp ha b, mul_inv_cancel_right]
    _ = ⁅a, b⁆⁻¹ := by simp only [commutatorElement_def]; group

private theorem commutator_cube {E : Type*} [Group E] (a b : E)
    (hb : b ^ 3 ∈ Subgroup.center E)
    (hz : a * b * a⁻¹ * b ∈ Subgroup.center E) : ⁅a, b⁆ ^ 3 = 1 := by
  have hzcomm : Commute (a * b * a⁻¹ * b) b :=
    (Subgroup.mem_center_iff.mp hz b).symm
  have hab : Commute (a * b * a⁻¹) b := by
    have h := hzcomm.mul_left (Commute.refl b).inv_left
    simpa only [mul_inv_cancel_right] using h
  calc
    ⁅a, b⁆ ^ 3 = (a * b * a⁻¹) ^ 3 * (b⁻¹) ^ 3 := hab.inv_right.mul_pow 3
    _ = (a * b ^ 3 * a⁻¹) * (b ^ 3)⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply, inv_pow]
    _ = 1 := by
      rw [Subgroup.mem_center_iff.mp hb a]
      group

private theorem normalizes_zpowers_of_inverts {E : Type*} [Group E] (a c : E)
    (h : a * c * a⁻¹ = c⁻¹) : a ∈ Subgroup.normalizer (Subgroup.zpowers c : Set E) := by
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  change ((Subgroup.zpowers c).map (MulAut.conj a).toMonoidHom : Set E) = _
  rw [MonoidHom.map_zpowers]
  change (Subgroup.zpowers (a * c * a⁻¹) : Set E) = _
  rw [h, Subgroup.zpowers_inv]

/-- A six-normal-form criterion, proved directly for arbitrary central extensions.
The hypotheses are the standard involution/three-cycle description of `S₃`. -/
theorem schurTrivial_of_six_normal_forms {Q : Type} [Group Q] (s t : Q)
    (hs : s ^ 2 = 1) (ht : orderOf t = 3)
    (hst : s * t * s⁻¹ * t = 1) (hcst : ⁅s, t⁆ = t)
    (hnf : ∀ q : Q, ∃ i j : ℕ, q = t ^ j * s ^ i) : SchurTrivial Q := by
  apply (schurTrivial_iff_centralDerivedInjective Q).mpr
  intro E _ π hπ hc x hx hxπ
  obtain ⟨a, ha⟩ := hπ s
  obtain ⟨b, hb⟩ := hπ t
  let c := ⁅a, b⁆
  have hpc : π c = t := by simp [c, map_commutatorElement, ha, hb, hcst]
  have ha2 : a ^ 2 ∈ Subgroup.center E := hc (by
    rw [MonoidHom.mem_ker, map_pow, ha, hs])
  have hb3 : b ^ 3 ∈ Subgroup.center E := hc (by
    rw [MonoidHom.mem_ker, map_pow, hb, ← ht, pow_orderOf_eq_one])
  have hz : a * b * a⁻¹ * b ∈ Subgroup.center E := hc (by
    simpa [MonoidHom.mem_ker, ha, hb] using hst)
  have hc3 : c ^ 3 = 1 := commutator_cube a b hb3 hz
  have hnfa : ∀ e : E, ∃ z ∈ Subgroup.center E, ∃ i j : ℕ,
      e = z * (c ^ j * a ^ i) := by
    intro e
    obtain ⟨i, j, hij⟩ := hnf (π e)
    refine ⟨e * (c ^ j * a ^ i)⁻¹, hc ?_, i, j, by group⟩
    simp [MonoidHom.mem_ker, hpc, ha, hij]
  let K := Subgroup.zpowers c
  have haN : a ∈ Subgroup.normalizer (K : Set E) :=
    normalizes_zpowers_of_inverts a c (conjugate_commutator a b ha2)
  have hKN : Subgroup.normalizer (K : Set E) = ⊤ := by
    apply top_unique
    intro e _
    obtain ⟨z, hz, i, j, rfl⟩ := hnfa e
    exact mul_mem (Subgroup.center_le_normalizer _ hz)
      (mul_mem (Subgroup.le_normalizer (Subgroup.npow_mem_zpowers c j)) (pow_mem haN i))
  haveI : K.Normal := Subgroup.normalizer_eq_top_iff.mp hKN
  let f : E →* E ⧸ K := QuotientGroup.mk' K
  have hfc : f c = 1 := (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_zpowers c)
  have hfz : ∀ z ∈ Subgroup.center E, ∀ y : E ⧸ K, Commute (f z) y := by
    intro z hz y
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective K y
    exact ((show Commute z e from (Subgroup.mem_center_iff.mp hz e).symm).map f)
  have hfcomm : ∀ e d : E, Commute (f e) (f d) := by
    intro e d
    obtain ⟨z, hz, i, j, rfl⟩ := hnfa e
    obtain ⟨w, hw, k, l, rfl⟩ := hnfa d
    simp only [map_mul, map_pow, hfc, one_pow, one_mul]
    exact ((hfz z hz _).mul_right (hfz z hz _)).mul_left
      (((hfz w hw _).symm).mul_right ((Commute.refl (f a)).pow_pow i k))
  have hderived : commutator E ≤ K := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨e, d, rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅e, d⁆ = 1
    rw [map_commutatorElement]
    exact (hfcomm e d).commutator_eq
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hderived hx)
  have htn : t ^ n = 1 := by simpa [hpc] using hxπ
  have hn : (3 : ℤ) ∣ n := by
    simpa [ht] using (orderOf_dvd_iff_zpow_eq_one.mpr htn)
  obtain ⟨m, rfl⟩ := hn
  rw [zpow_mul, zpow_ofNat, hc3, one_zpow]

end VOA.Huang.DLNSchur
