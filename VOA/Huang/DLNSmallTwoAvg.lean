import VOA.Huang.DLNSmallTwoLayer
import VOA.Huang.DLNSmallAverage2

/-!
# The `C₃`-average of the two-adic layer lies in `{1, ε}`
-/

namespace VOA.Huang.DLNSchur

open VOA.Huang.DLNBeyl

section TwoAvg

variable {a : ℕ}

theorem list_prod_one_add_smul_two {ι : Type*} (q : ZMod (2 ^ (a + 1))) (hq : q * q = 0)
    (L : List ι) (f : ι → SLT a) (Wf : ι → Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1))))
    (h : ∀ i ∈ L, (f i : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) = 1 + q • Wf i) :
    (((L.map f).prod : SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      1 + q • (L.map Wf).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    rw [List.map_cons, List.prod_cons, Matrix.SpecialLinearGroup.coe_mul,
      h b (by simp), ih (fun i hi => h i (by simp [hi])), one_add_smul_mul_one_add_smul, hq,
      zero_smul, add_zero, List.map_cons, List.sum_cons, smul_add, add_assoc]

/-- **The `C₃`-average sends the layer into `{1, ε}`.** -/
theorem layerTwo_c3_average (ha : 1 ≤ a)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) → SLT a)
    (hg : ∀ q ∈ c3Finset, rhoTwoOne a (g q) = q) (n : SLT a) (hn : n ∈ (rhoTwo a).ker) :
    (c3Finset.toList.map (fun q => g q * n * (g q)⁻¹)).prod ∈ Subgroup.zpowers (eps2 a) := by
  obtain ⟨W, hW⟩ := (mem_ker_rhoTwo_iff n).mp hn
  set q : ZMod (2 ^ (a + 1)) := 2 ^ a with hqdef
  have hq : q * q = 0 := two_pow_mul_self ha
  let Wf : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) → Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1))) :=
    fun s => (g s : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) * W * ((g s)⁻¹ : SLT a)
  have hterm : ∀ s ∈ c3Finset.toList,
      ((g s * n * (g s)⁻¹ : SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
        1 + q • Wf s := by
    intro s _
    have hinv : (g s : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) * ((g s)⁻¹ : SLT a) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    simp only [Matrix.SpecialLinearGroup.coe_mul, hW, Wf]
    rw [mul_add, add_mul, mul_one, hinv, Matrix.mul_smul, Matrix.smul_mul]
  have hprod := list_prod_one_add_smul_two q hq _ _ Wf hterm
  set F := (ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero a)) (ZMod 2)).mapMatrix
    (m := Fin 2) with hF
  have hmapG : ∀ s ∈ c3Finset, F (g s : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      (s : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    intro s hs
    have : (s : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
        (rhoTwoOne a (g s) : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by rw [hg s hs]
    rw [this]; rfl
  have hmapGi : ∀ s ∈ c3Finset,
      F (((g s)⁻¹ : SLT a) : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) =
      ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    intro s hs
    have : ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) =
        (rhoTwoOne a ((g s)⁻¹) : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
      rw [map_inv, hg s hs]
    rw [this]; rfl
  have hdet : (n : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))).det = 1 := n.2
  rw [hW, Matrix.det_fin_two] at hdet
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), zero_add] at hdet
  have htr0 : q * (W 0 0 + W 1 1) = 0 := by
    linear_combination hdet - (W 0 0 * W 1 1 - W 0 1 * W 1 0) * hq
  have htr : (F W).trace = 0 := by
    rw [Matrix.trace_fin_two]
    have := (two_pow_mul_eq_zero_iff (W 0 0 + W 1 1)).mp htr0
    rw [map_add] at this
    exact this
  have hsum : F (c3Finset.toList.map Wf).sum = ∑ s ∈ c3Finset, (s : Matrix (Fin 2) (Fin 2) (ZMod 2)) *
      F W * ((s⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
    rw [map_list_sum, List.map_map, Finset.sum_map_toList]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Function.comp, Wf, map_mul, hmapG s hs, hmapGi s hs]
  -- entrywise: `q * x = q * y` when `x ≡ y (mod 2)`
  have hentry : ∀ (S : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1))))
      (T : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))), F S = F T → q • S = q • T := by
    intro S T hST
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
    apply (two_pow_mul_eq_zero_iff _).mpr
    rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun hST i) j
  rcases c3_average_aux (F W) htr with h0 | h1
  · have : q • (c3Finset.toList.map Wf).sum = q • (0 : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) :=
      hentry _ _ (by rw [hsum, h0, map_zero])
    have hone : (c3Finset.toList.map (fun q => g q * n * (g q)⁻¹)).prod = 1 := by
      apply Subtype.ext
      rw [hprod, this, smul_zero, add_zero, Matrix.SpecialLinearGroup.coe_one]
    rw [hone]; exact one_mem _
  · have : q • (c3Finset.toList.map Wf).sum = q • (1 : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ (a + 1)))) :=
      hentry _ _ (by rw [hsum, h1, map_one])
    have heps : (c3Finset.toList.map (fun q => g q * n * (g q)⁻¹)).prod = eps2 a := by
      apply Subtype.ext
      rw [hprod, this, eps2_coe ha]
    rw [heps]; exact Subgroup.mem_zpowers _

end TwoAvg

end VOA.Huang.DLNSchur
