import VOA.Huang.DLNSmallThreeGen

/-!
# The quaternion average kills the layer

Let `Q₈ = {g ∈ SL₂(ℤ/3) | g⁴ = 1}`. For any lifts `g_q ∈ SL₂(ℤ/3^{k+1})` of the elements of
`Q₈`, and any `n` in the layer `N`, the product `∏_q g_q n g_q⁻¹` is trivial. Writing
`n = 1 + 3^k W`, the product is `1 + 3^k Σ_q g_q W g_q⁻¹`, and modulo 3 the sum is the
quaternion average of the traceless matrix `W mod 3`, which vanishes.
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

/-- The quaternion subgroup of `SL₂(ℤ/3)` as a finite set. -/
def quatFinset : Finset SLThree := Finset.univ.filter (fun g => g ^ 4 = 1)

theorem quatFinset_card : quatFinset.card = 8 := by decide +kernel

theorem quatFinset_conj (s q : SLThree) (hq : q ∈ quatFinset) : s⁻¹ * q * s ∈ quatFinset := by
  simp only [quatFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
  have : s⁻¹ * q * s = MulAut.conj s⁻¹ q := by simp
  rw [this, ← map_pow, hq, map_one]

theorem quatFinset_average_aux : ∀ W : Matrix (Fin 2) (Fin 2) (ZMod 3), W.trace = 0 →
    ∑ q ∈ quatFinset, (q : Matrix (Fin 2) (Fin 2) (ZMod 3)) * W *
      ((q⁻¹ : SLThree) : Matrix (Fin 2) (Fin 2) (ZMod 3)) = 0 := by
  decide +kernel

section Avg

variable {k : ℕ}

theorem three_pow_mul_eq_zero_iff (r : ZMod (3 ^ (k + 1))) :
    (3 : ZMod (3 ^ (k + 1))) ^ k * r = 0 ↔
      ZMod.castHom (dvd_pow_self 3 (Nat.succ_ne_zero k)) (ZMod 3) r = 0 := by
  constructor
  · intro h
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    have h' : ((3 ^ k * r.val : ℕ) : ZMod (3 ^ (k + 1))) = 0 := by
      push_cast; rw [ZMod.natCast_zmod_val]; exact h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact Nat.dvd_of_mul_dvd_mul_left (by positivity) (dvd_trans ⟨1, by ring⟩ h')
  · intro h
    obtain ⟨w, rfl⟩ := (castHom_eq_zero_iff_exists _ r).mp h
    push_cast
    rw [← mul_assoc, ← pow_succ, three_pow_succ_eq_zero, zero_mul]

theorem list_prod_one_add_smul {ι : Type*} (q : ZMod (3 ^ (k + 1))) (hq : q * q = 0)
    (L : List ι) (f : ι → SLL k) (Wf : ι → Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1))))
    (h : ∀ i ∈ L, (f i : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) = 1 + q • Wf i) :
    (((L.map f).prod : SLL k) : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) =
      1 + q • (L.map Wf).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul,
      h a (by simp), ih (fun i hi => h i (by simp [hi])), one_add_smul_mul_one_add_smul, hq,
      zero_smul, add_zero, List.map_cons, List.sum_cons, smul_add, add_assoc]

/-- **The quaternion average kills the layer.** -/
theorem layer_quat_average (hk : 1 ≤ k) (g : SLThree → SLL k)
    (hg : ∀ q ∈ quatFinset, rhoOne k (g q) = q) (n : SLL k) (hn : n ∈ layerN k) :
    (quatFinset.toList.map (fun q => g q * n * (g q)⁻¹)).prod = 1 := by
  obtain ⟨W, hW⟩ := (mem_layerN_iff n).mp hn
  set q : ZMod (3 ^ (k + 1)) := 3 ^ k with hqdef
  have hq : q * q = 0 := three_pow_mul_self hk
  let Wf : SLThree → Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1))) := fun s =>
    (g s : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) * W *
      ((g s)⁻¹ : SLL k)
  have hterm : ∀ s ∈ quatFinset.toList,
      ((g s * n * (g s)⁻¹ : SLL k) : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) =
        1 + q • Wf s := by
    intro s _
    have hinv : (g s : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) * ((g s)⁻¹ : SLL k) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, hW, Wf]
    rw [mul_add, add_mul, mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul]
  apply Subtype.ext
  rw [list_prod_one_add_smul q hq _ _ Wf hterm, Matrix.SpecialLinearGroup.coe_one]
  -- It remains to show `q • Σ Wf = 0`, which we check modulo 3.
  set F := (ZMod.castHom (dvd_pow_self 3 (Nat.succ_ne_zero k)) (ZMod 3)).mapMatrix
    (m := Fin 2) with hF
  have hmapG : ∀ s ∈ quatFinset, F (g s : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) =
      (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    intro s hs
    have : (s : Matrix (Fin 2) (Fin 2) (ZMod 3)) = (rhoOne k (g s) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      rw [hg s hs]
    rw [this]; rfl
  have hmapGi : ∀ s ∈ quatFinset, F (((g s)⁻¹ : SLL k) : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))) =
      ((s⁻¹ : SLThree) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
    intro s hs
    have : ((s⁻¹ : SLThree) : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        (rhoOne k ((g s)⁻¹) : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
      rw [map_inv, hg s hs]
    rw [this]; rfl
  -- trace of `W` vanishes modulo 3
  have hdet : (n : Matrix (Fin 2) (Fin 2) (ZMod (3 ^ (k + 1)))).det = 1 := n.2
  rw [hW, Matrix.det_fin_two] at hdet
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add] at hdet
  have htr0 : q * (W 0 0 + W 1 1) = 0 := by
    linear_combination hdet - (W 0 0 * W 1 1 - W 0 1 * W 1 0) * hq
  have htr : (F W).trace = 0 := by
    rw [Matrix.trace_fin_two]
    have := (three_pow_mul_eq_zero_iff (W 0 0 + W 1 1)).mp htr0
    rw [map_add] at this
    exact this
  have havg := quatFinset_average_aux (F W) htr
  have hsum : F (quatFinset.toList.map Wf).sum = 0 := by
    rw [map_list_sum, List.map_map, Finset.sum_map_toList]
    rw [← havg]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Function.comp, Wf, map_mul, hmapG s hs, hmapGi s hs]
  have hzero : q • (quatFinset.toList.map Wf).sum = 0 := by
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    apply (three_pow_mul_eq_zero_iff _).mpr
    have := congrFun (congrFun hsum i) j
    exact this
  rw [hzero, add_zero]

end Avg

end VOA.Huang.DLNSchur
