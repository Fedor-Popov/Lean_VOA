/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.LatticeTwistedVertex
import VOA.Moonshine.LatticeTwistedAssoc
import VOA.Moonshine.HeisenbergTwistedModuleWords

/-!
# The twisted vertex operator on all of `V_L`  (Moonshine step M6)

The rescaled twisted fields `F_e(u)` (`p`-th mode `u₍(2p+e)/2₎`) are extended from the
exponentials `e^α` (`YTLFld`, `LatticeTwistedVertex`) to all of `V_L = FockN ⊗ ℂ{L}` by the
inversion of the twisted product formula against the twisted Heisenberg generators:

  `F_e(h_b(−n−1) w) = star ½ (Fgen_b) (−n−1) F_{e−1}(w)`.

* `rTFld` — tensoring a field on `S[θ]` with `T`; it is a homomorphism for the nonnegative
  products (`prod_rTFld_nonneg`), which transports the generator OPE (`prod_FgT_zero` etc.,
  `star_gT_gen`).
* `Fw α l e` — the word fields, in the generated twisted system (`Fw_mem`), shift covariant
  (`Fw_add_two`), independent of the order of the letters (`Fw_perm`), with the charge
  conjugation `Fw (−α) l e = (−1)^{e+|l|} Fw α l e` (`Fw_neg`).
* `FL e : V_L →ₗ Fld (S[θ] ⊗ T)` — the linear extension through the monomial basis, with
  `FL_wordState`, the creation formula `FL_mul_X`, the shift `FL_shift` and the involution
  `FL_theta` (`F_e(θu) = (−1)ᵉ F_e(u)`).
* `YML : V_L →ₗ (ℤ → End (S[θ] ⊗ T))`, `YML u k = u₍k/2₎`, with `resc_YML` (`= F_e`),
  `YML_truncation`, `YML_vacuum`, `YML_support` (the support condition for `θ`) and
  `YML_local` (all rescaled fields mutually local).

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
-/

namespace VOA.Moonshine.LatticeTwisted

open MvPolynomial TwistedHeisenberg TwistedReduction HeisenbergN
open Module (End)
open scoped BigOperators TensorProduct

/-! ## Tensoring fields with `T` -/

section RT

variable {r : ℕ} {Tm : Type*} [AddCommGroup Tm] [Module ℂ Tm]

theorem rTensor_isField {A : FormalDist (End ℂ (FockT r))} (hA : IsField A) :
    IsField (fun n => (A n).rTensor Tm) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, fun n _ => map_zero _⟩
  | tmul y t =>
      obtain ⟨B, hB⟩ := hA y
      exact ⟨B, fun n hn => by rw [LinearMap.rTensor_tmul, hB n hn, TensorProduct.zero_tmul]⟩
  | add x₁ x₂ h₁ h₂ =>
      obtain ⟨B₁, hB₁⟩ := h₁
      obtain ⟨B₂, hB₂⟩ := h₂
      exact ⟨min B₁ B₂, fun n hn => by
        rw [map_add, hB₁ n (lt_of_lt_of_le hn (min_le_left _ _)),
          hB₂ n (lt_of_lt_of_le hn (min_le_right _ _)), add_zero]⟩

/-- A field on `S[θ]`, tensored with `T`. -/
noncomputable def rTFld (A : Fld (FockT r)) : Fld (FockT r ⊗[ℂ] Tm) :=
  ⟨fun n => (A.1 n).rTensor Tm, rTensor_isField A.2⟩

@[simp] theorem rTFld_val (A : Fld (FockT r)) (n : ℤ) :
    (rTFld (Tm := Tm) A).1 n = (A.1 n).rTensor Tm := rfl

theorem rTFld_smul (c : ℂ) (A : Fld (FockT r)) : rTFld (Tm := Tm) (c • A) = c • rTFld A := by
  apply Subtype.ext; funext n
  change ((c • A.1 n)).rTensor Tm = c • (A.1 n).rTensor Tm
  rw [LinearMap.rTensor_smul]

theorem rTFld_zero : rTFld (Tm := Tm) (0 : Fld (FockT r)) = 0 := by
  apply Subtype.ext; funext n
  change ((0 : End ℂ (FockT r))).rTensor Tm = 0
  rw [LinearMap.rTensor_zero]

theorem rTFld_one : rTFld (Tm := Tm) (Fld.one : Fld (FockT r)) = Fld.one := by
  apply Subtype.ext; funext n
  change ((idField : FormalDist (End ℂ (FockT r))) n).rTensor Tm = idField n
  rw [idField_apply, idField_apply]
  split_ifs
  · exact LinearMap.rTensor_id _ _
  · exact LinearMap.rTensor_zero _

theorem rTFld_fzmul (c : ℤ) (A : Fld (FockT r)) :
    rTFld (Tm := Tm) (fzmul c A) = fzmul c (rTFld A) := rfl

/-- Tensoring with `T` is a homomorphism for the nonnegative field products. -/
theorem prod_rTFld_nonneg (n : ℕ) (A B : Fld (FockT r)) :
    Fld.prod n (rTFld (Tm := Tm) A) (rTFld B) = rTFld (Fld.prod n A B) := by
  apply Subtype.ext
  rw [Fld.prod_of_nonneg (by omega), Int.toNat_natCast]
  funext t
  change cCoeff n (bracketDist (rTFld (Tm := Tm) A).1 (rTFld (Tm := Tm) B).1) t
    = ((Fld.prod n A B).1 t).rTensor Tm
  rw [Fld.prod_of_nonneg (by omega), Int.toNat_natCast]
  have hb : bracketDist (rTFld (Tm := Tm) A).1 (rTFld (Tm := Tm) B).1
      = fun m k => (bracketDist A.1 B.1 m k).rTensor Tm := by
    funext m k
    rw [bracketDist_apply, bracketDist_apply, LinearMap.rTensor_sub, LinearMap.rTensor_mul,
      LinearMap.rTensor_mul]
    rfl
  rw [hb, cCoeff_apply, cCoeff_apply,
    mulBySubPow_map (fun f => f.rTensor Tm) (fun f g => LinearMap.rTensor_sub f g)]

/-! ## The twisted Heisenberg generators on `S[θ] ⊗ T` -/

/-- The rescaled generator `z^{1/2} h_a(z) ⊗ 1` as a field. -/
noncomputable def FgT (a : Fin r) : Fld (FockT r ⊗[ℂ] Tm) := rTFld (Moonshine.FgenFld r a)

theorem FgT_val (a : Fin r) : (FgT (Tm := Tm) a).1 = FgenT a := rfl

theorem prod_FgT_two_le (a b : Fin r) {n : ℤ} (hn : 2 ≤ n) :
    Fld.prod n (FgT (Tm := Tm) a) (FgT b) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by omega⟩
  rw [FgT, FgT, prod_rTFld_nonneg, Moonshine.prod_Fgen_two_le_fld r a b hn, rTFld_zero]

theorem prod_FgT_one (a b : Fin r) :
    Fld.prod 1 (FgT (Tm := Tm) a) (FgT b)
      = (if a = b then (1 : ℂ) else 0) • fzmul 1 (Fld.one : Fld (FockT r ⊗[ℂ] Tm)) := by
  rw [FgT, FgT, show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, prod_rTFld_nonneg,
    show ((1 : ℕ) : ℤ) = 1 by norm_num, Moonshine.prod_Fgen_one_fld, rTFld_smul, rTFld_fzmul,
    rTFld_one]

theorem prod_FgT_zero (a b : Fin r) :
    Fld.prod 0 (FgT (Tm := Tm) a) (FgT b)
      = (if a = b then (1 / 2 : ℂ) else 0) • (Fld.one : Fld (FockT r ⊗[ℂ] Tm)) := by
  rw [FgT, FgT, show (0 : ℤ) = ((0 : ℕ) : ℤ) by norm_num, prod_rTFld_nonneg,
    show ((0 : ℕ) : ℤ) = 0 by norm_num, Moonshine.prod_Fgen_zero_fld, rTFld_smul, rTFld_one]

/-- **The twisted products of two generators** on `S[θ] ⊗ T`. -/
theorem star_gT_gen (a b : Fin r) (i : ℕ) :
    star (1 / 2) (FgT (Tm := Tm) a) i (FgT b)
      = if i = 1 then (if a = b then (1 : ℂ) else 0) •
          fzmul 1 (Fld.one : Fld (FockT r ⊗[ℂ] Tm)) else 0 := by
  rw [star_eq_sum_range _ _ _ _ 2 (fun j hj => prod_FgT_two_le a b (by omega))]
  rcases i with _ | _ | i
  · rw [if_neg (by norm_num), Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero, Nat.cast_one, add_zero, zero_add, neg_zero, cbinom_zero, one_smul,
      fzmul_zero_shift]
    have h1 : cbinom (-(1 / 2)) 1 = -(1 / 2) := by simp [cbinom]
    rw [prod_FgT_zero, prod_FgT_one, h1, fzmul_smul, fzmul_fzmul,
      show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift, smul_smul]
    split_ifs <;> module
  · rw [if_pos rfl, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.cast_zero, Nat.cast_one, add_zero, neg_zero, cbinom_zero, one_smul,
      fzmul_zero_shift]
    rw [show ((0 + 1 : ℕ) : ℤ) = 1 by norm_num, prod_FgT_one, show (1 : ℤ) + 1 = 2 by norm_num,
      prod_FgT_two_le a b (by norm_num), fzmul_zero, smul_zero, add_zero]
  · rw [Finset.sum_eq_zero (fun j _ => by rw [prod_FgT_two_le a b (by omega), fzmul_zero,
      smul_zero]), if_neg (by omega)]

end RT

/-! ## The word fields over `e^α` -/

section Lattice

open IntegralLattice LatGen Extraspecial

variable (L : IntegralLattice) (hEven : L.Even) (hU : IsUnit (gramMat L).det)

/-- The twisted module `V_L^T = S[θ] ⊗ T`. -/
abbrev MT : Type := FockT (rank L) ⊗[ℂ] Rep (cocMat L) (isUnit_det_cocMat L hEven hU)

theorem FgenTFld_eq_FgT (a : Fin (rank L)) : FgenTFld L hEven hU a = FgT a := rfl

/-- **The word fields** `F_e(h_{b₁}(−n₁−1)⋯h_{b_k}(−n_k−1) e^α)`, by inverting the twisted
product formula against the generators. -/
noncomputable def Fw (α : L.carrier) : List (ℕ × Fin (rank L)) → ℤ → Fld (MT L hEven hU)
  | [], e => YTLFld L hEven hU α e
  | (c :: l), e => star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (Fw α l (e - 1))

@[simp] theorem Fw_nil (α : L.carrier) (e : ℤ) : Fw L hEven hU α [] e = YTLFld L hEven hU α e :=
  rfl

theorem Fw_cons (α : L.carrier) (c : ℕ × Fin (rank L)) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven hU α (c :: l) e = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (Fw L hEven hU α l (e - 1)) :=
  rfl

theorem FgT_mem (a : Fin (rank L)) :
    FgT a ∈ TGenerated (latGenSet L hEven hU) :=
  subset_tgenerated (Set.mem_union_left _ ⟨a, rfl⟩)

theorem YTLFld_mem (α : L.carrier) (e : ℤ) :
    YTLFld L hEven hU α e ∈ TGenerated (latGenSet L hEven hU) :=
  subset_tgenerated (Set.mem_union_right _ ⟨(α, e), rfl⟩)

variable (hPos : L.PosDef)
include hPos

theorem Fw_mem (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven hU α l e ∈ TGenerated (latGenSet L hEven hU) := by
  induction l generalizing e with
  | nil => exact YTLFld_mem L hEven hU α e
  | cons c l ih =>
      exact star_mem (latGenSet_local L hEven hU hPos) (FgT_mem L hEven hU c.2) (ih _) _ _

theorem tloc {X Y : Fld (MT L hEven hU)} (hX : X ∈ TGenerated (latGenSet L hEven hU))
    (hY : Y ∈ TGenerated (latGenSet L hEven hU)) : Local X.1 Y.1 :=
  latticeTwistedSystem_local L hEven hU hPos hX hY

omit hPos in
theorem YTLFld_add_two (α : L.carrier) (e : ℤ) :
    YTLFld L hEven hU α (e + 2) = fzmul 1 (YTLFld L hEven hU α e) :=
  Subtype.ext (resc_add_N (YTL L hEven hU α) 2 e)

omit hPos in
/-- Moving the class by `2` multiplies by `z`. -/
theorem Fw_add_two (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven hU α l (e + 2) = fzmul 1 (Fw L hEven hU α l e) := by
  induction l generalizing e with
  | nil => exact YTLFld_add_two L hEven hU α e
  | cons c l ih =>
      rw [Fw_cons, Fw_cons, show e + 2 - 1 = (e - 1) + 2 by ring, ih, star_fzmul_right]

omit hPos in
theorem Fw_shift (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e c : ℤ) :
    Fw L hEven hU α l (e + 2 * c) = fzmul c (Fw L hEven hU α l e) := by
  induction c using Int.induction_on with
  | zero => simp
  | succ c ih =>
      rw [show e + 2 * (c + 1) = (e + 2 * c) + 2 by ring, Fw_add_two, ih, fzmul_fzmul, add_comm]
  | pred c ih =>
      have h := Fw_add_two L hEven hU α l (e + 2 * (-(c : ℤ) - 1))
      rw [show e + 2 * (-(c : ℤ) - 1) + 2 = e + 2 * (-(c : ℤ)) by ring, ih] at h
      have h' := congrArg (fzmul (-1)) h
      rw [fzmul_fzmul, fzmul_fzmul, show (-1 : ℤ) + 1 = 0 by norm_num, fzmul_zero_shift] at h'
      rw [← h', show (-1 : ℤ) + -(c : ℤ) = -(c : ℤ) - 1 by ring]

/-- Two creation twisted products of generators commute. -/
theorem star_gT_swap (c c' : ℕ × Fin (rank L)) {F : Fld (MT L hEven hU)}
    (hF : F ∈ TGenerated (latGenSet L hEven hU)) :
    star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (star (1 / 2) (FgT c'.2) (-(c'.1 : ℤ) - 1) F)
      = star (1 / 2) (FgT c'.2) (-(c'.1 : ℤ) - 1)
          (star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) F) := by
  have h := star_comm (latGenSet_local L hEven hU hPos) (FgT_mem L hEven hU c.2)
    (FgT_mem L hEven hU c'.2) hF (1 / 2) (1 / 2)
    (-(c.1 : ℤ) - 1) (-(c'.1 : ℤ) - 1) 2 (fun s hs => prod_FgT_two_le _ _ (by omega))
  rw [Finset.sum_range_succ, Finset.sum_range_one, star_gT_gen, star_gT_gen, if_neg (by norm_num),
    if_pos (by norm_num), star_zero_left, smul_zero, zero_add,
    star_smul_left (local_fzmul_one_left 1 F),
    show (1 / 2 : ℂ) + 1 / 2 = ((1 : ℤ) : ℂ) by norm_num, star_fzmul_one,
    if_neg (show -(c.1 : ℤ) - 1 + (-(c'.1 : ℤ) - 1) - ((1 : ℕ) : ℤ) ≠ -1 by push_cast; omega),
    smul_zero, smul_zero] at h
  exact sub_eq_zero.mp h

/-- **The word fields depend only on the multiset of letters.** -/
theorem Fw_perm (α : L.carrier) {l l' : List (ℕ × Fin (rank L))} (h : l.Perm l') (e : ℤ) :
    Fw L hEven hU α l e = Fw L hEven hU α l' e := by
  induction h generalizing e with
  | nil => rfl
  | cons x _ ih => rw [Fw_cons, Fw_cons, ih]
  | swap x y l =>
      rw [Fw_cons, Fw_cons, Fw_cons, Fw_cons, star_gT_swap L hEven hU hPos y x
        (Fw_mem L hEven hU hPos α l _)]
  | trans _ _ ih₁ ih₂ => exact (ih₁ e).trans (ih₂ e)

omit hPos in
theorem YTLFld_neg (α : L.carrier) (e : ℤ) :
    YTLFld L hEven hU (-α) e = ((-1 : ℂ) ^ e) • YTLFld L hEven hU α e := by
  apply fld_ext_mode
  intro p x
  change mode (resc (YTL L hEven hU (-α)) 2 e) p x = mode ((-1 : ℂ) ^ e • resc (YTL L hEven hU α) 2 e) p x
  rw [mode_resc, mode_smul, mode_resc, YTL_neg, neg_one_zpow_congr (b := e) (by omega)]

/-- **Charge conjugation of the word fields.** -/
theorem Fw_neg (α : L.carrier) (l : List (ℕ × Fin (rank L))) (e : ℤ) :
    Fw L hEven hU (-α) l e = ((-1 : ℂ) ^ (e + l.length)) • Fw L hEven hU α l e := by
  induction l generalizing e with
  | nil => rw [Fw_nil, Fw_nil, YTLFld_neg, List.length_nil, Nat.cast_zero, add_zero]
  | cons c l ih =>
      rw [Fw_cons, Fw_cons, ih, star_smul_right (tloc L hEven hU hPos (FgT_mem L hEven hU c.2)
        (Fw_mem L hEven hU hPos α l _)), List.length_cons]
      congr 1
      exact neg_one_zpow_congr (by push_cast; omega)

/-! ## The linear extension `F_e : V_L → Fld (S[θ] ⊗ T)` -/

/-- The bilinear form of `F_e` on `FockN ⊗ ℂ{L}`. -/
noncomputable def FLB (e : ℤ) :
    FockN (rank L) →ₗ[ℂ] (L.carrier →₀ ℂ) →ₗ[ℂ] Fld (MT L hEven hU) :=
  Finsupp.linearCombination ℂ (fun m : (ℕ × Fin (rank L)) →₀ ℕ =>
    Finsupp.linearCombination ℂ (fun α : L.carrier => Fw L hEven hU α (monoWordN m) e))

/-- **The rescaled twisted vertex operator** `F_e : V_L →ₗ Fld (S[θ] ⊗ T)`. -/
noncomputable def FL (e : ℤ) : LatModuleGen L →ₗ[ℂ] Fld (MT L hEven hU) :=
  TensorProduct.lift (FLB L hEven hU e)

omit hPos in
theorem FL_monomial (e : ℤ) (m : (ℕ × Fin (rank L)) →₀ ℕ) (a : ℂ) (α : L.carrier) (c : ℂ) :
    FL L hEven hU e (monomial m a ⊗ₜ[ℂ] Finsupp.single α c)
      = (a * c) • Fw L hEven hU α (monoWordN m) e := by
  rw [FL, TensorProduct.lift.tmul]
  have h1 : FLB L hEven hU e (monomial m a)
      = a • Finsupp.linearCombination ℂ (fun α : L.carrier => Fw L hEven hU α (monoWordN m) e) :=
    Finsupp.linearCombination_single ℂ a m
  rw [h1, LinearMap.smul_apply, Finsupp.linearCombination_single, smul_smul]

omit hPos in
theorem FL_monomial_eGen (e : ℤ) (m : (ℕ × Fin (rank L)) →₀ ℕ) (α : L.carrier) :
    FL L hEven hU e (monomial m 1 ⊗ₜ[ℂ] eGen L α) = Fw L hEven hU α (monoWordN m) e := by
  rw [eGen, FL_monomial, one_mul, one_smul]

omit hEven hU hPos in
theorem wordStateN_perm {l l' : List (ℕ × Fin (rank L))} (h : l.Perm l') :
    wordStateN l = wordStateN l' := by
  rw [wordStateN, wordStateN]
  exact (h.map _).prod_eq

/-- `F_e` on a word state is the word field. -/
theorem FL_wordState (e : ℤ) (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    FL L hEven hU e (wordStateN l ⊗ₜ[ℂ] eGen L α) = Fw L hEven hU α l e := by
  set m : (ℕ × Fin (rank L)) →₀ ℕ := Multiset.toFinsupp (l : Multiset (ℕ × Fin (rank L)))
  have hp : (monoWordN m).Perm l := by
    rw [← Multiset.coe_eq_coe, Moonshine.coe_monoWordN, Multiset.toFinsupp_toMultiset]
  rw [← wordStateN_perm L hp, wordStateN_monoWordN, FL_monomial_eGen, Fw_perm L hEven hU hPos α hp]

theorem FL_mem (e : ℤ) (u : LatModuleGen L) :
    FL L hEven hU e u ∈ TGenerated (latGenSet L hEven hU) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem_tgenerated _
  | add x y hx hy => rw [map_add]; exact add_mem_tgenerated hx hy
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem_tgenerated _
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add]; exact add_mem_tgenerated h₁ h₂
          | single α c =>
              rw [FL_monomial]
              exact smul_mem_tgenerated _ (Fw_mem L hEven hU hPos α _ e)
      | add p q hp hq => rw [TensorProduct.add_tmul, map_add]; exact add_mem_tgenerated hp hq

theorem FL_local (e e' : ℤ) (u v : LatModuleGen L) :
    Local (FL L hEven hU e u).1 (FL L hEven hU e' v).1 :=
  tloc L hEven hU hPos (FL_mem L hEven hU hPos e u) (FL_mem L hEven hU hPos e' v)

/-- **Creation**: `F_{e+1}(X_c p ⊗ g) = star ½ (Fgen_b) (−n−1) F_e(p ⊗ g)` (`c = (n, b)`). -/
theorem FL_mul_X (e : ℤ) (c : ℕ × Fin (rank L)) (p : FockN (rank L)) (g : L.carrier →₀ ℂ) :
    FL L hEven hU (e + 1) ((X c * p) ⊗ₜ[ℂ] g)
      = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (FL L hEven hU e (p ⊗ₜ[ℂ] g)) := by
  have hl : ∀ u : LatModuleGen L, Local (FgT (Tm := Rep (cocMat L) (isUnit_det_cocMat L hEven hU))
      c.2).1 (FL L hEven hU e u).1 := fun u =>
    tloc L hEven hU hPos (FgT_mem L hEven hU c.2) (FL_mem L hEven hU hPos e u)
  induction p using MvPolynomial.induction_on' with
  | monomial m a =>
      rw [Moonshine.X_mul_monomial']
      induction g using Finsupp.induction_linear with
      | zero => rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, map_zero, map_zero,
          star_zero_right]
      | add g₁ g₂ h₁ h₂ =>
          rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, h₁, h₂,
            star_add_right (hl _) (hl _)]
      | single α d =>
          rw [FL_monomial, FL_monomial, star_smul_right (tloc L hEven hU hPos
              (FgT_mem L hEven hU c.2) (Fw_mem L hEven hU hPos α _ e)),
            Fw_perm L hEven hU hPos α (Moonshine.monoWordN_add_single_perm _ m c), Fw_cons,
            add_sub_cancel_right]
  | add p q hp hq =>
      rw [mul_add, TensorProduct.add_tmul, TensorProduct.add_tmul, map_add, map_add, hp, hq,
        star_add_right (hl _) (hl _)]

/-- Creation, for every state. -/
theorem FL_mulLeft (e : ℤ) (c : ℕ × Fin (rank L)) (w : LatModuleGen L) :
    FL L hEven hU (e + 1) ((LinearMap.mulLeft ℂ (X c : FockN (rank L))).rTensor _ w)
      = star (1 / 2) (FgT c.2) (-(c.1 : ℤ) - 1) (FL L hEven hU e w) := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, star_zero_right]
  | tmul p g => rw [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, FL_mul_X L hEven hU hPos]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add, star_add_right
        (tloc L hEven hU hPos (FgT_mem L hEven hU c.2) (FL_mem L hEven hU hPos e x))
        (tloc L hEven hU hPos (FgT_mem L hEven hU c.2) (FL_mem L hEven hU hPos e y))]

omit hPos in
/-- Moving the class by `2c` multiplies by `zᶜ`. -/
theorem FL_shift (e c : ℤ) (u : LatModuleGen L) :
    FL L hEven hU (e + 2 * c) u = fzmul c (FL L hEven hU e u) := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, fzmul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, fzmul_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, fzmul_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, fzmul_add]
          | single α d => rw [FL_monomial, FL_monomial, Fw_shift, fzmul_smul]
      | add p q hp hq => rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, fzmul_add]

/-- **`θ`-compatibility**: `F_e(θ u) = (−1)ᵉ F_e(u)`. -/
theorem FL_theta (e : ℤ) (u : LatModuleGen L) :
    FL L hEven hU e (thetaLat L u) = ((-1 : ℂ) ^ e) • FL L hEven hU e u := by
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]
  | tmul p g =>
      induction p using MvPolynomial.induction_on' with
      | monomial m a =>
          induction g using Finsupp.induction_linear with
          | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
          | add g₁ g₂ h₁ h₂ =>
              rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, map_add, smul_add]
          | single α d =>
              have hs : (monomial m a : FockN (rank L)) ⊗ₜ[ℂ] Finsupp.single α d
                  = (a * d) • ((monomial m 1 : FockN (rank L)) ⊗ₜ[ℂ] eGen L α) := by
                rw [eGen, show (monomial m a : FockN (rank L)) = a • monomial m 1 by
                    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
                  show (Finsupp.single α d : L.carrier →₀ ℂ) = d • Finsupp.single α 1 by
                    rw [Finsupp.smul_single_one],
                  TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm d a]
              rw [hs, map_smul, map_smul, map_smul, thetaLat_tmul, Moonshine.sigmaN_monomial_length,
                ← TensorProduct.smul_tmul', map_smul, FL_monomial_eGen, FL_monomial_eGen,
                Fw_neg L hEven hU hPos, smul_smul, smul_smul, smul_comm ((-1 : ℂ) ^ e), smul_smul]
              have hpow : ((-1 : ℂ) ^ (monoWordN m).length) * ((-1 : ℂ) ^ (monoWordN m).length)
                  = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
              congr 1
              rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
              linear_combination (a * d * (-1 : ℂ) ^ e) * hpow
      | add p q hp hq =>
          rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, map_add, smul_add]

/-! ## The twisted vertex operator `Y^T` on `V_L` -/

/-- **The twisted vertex operator** `Y^T(u)₍k/2₎ = mode₀ F_k(u)`. -/
noncomputable def YML : LatModuleGen L →ₗ[ℂ] (ℤ → End ℂ (MT L hEven hU)) :=
  LinearMap.pi (fun k => (modeL 0).comp (FL L hEven hU k))

omit hPos in
theorem YML_apply (u : LatModuleGen L) (k : ℤ) : YML L hEven hU u k = mode (FL L hEven hU k u).1 0 :=
  rfl

omit hPos in
/-- The rescaled `Y^T` on the class `e` is `F_e`. -/
theorem resc_YML (u : LatModuleGen L) (e : ℤ) : resc (YML L hEven hU u) 2 e = (FL L hEven hU e u).1 := by
  funext n
  rw [resc, YML_apply, show ((2 : ℕ) : ℤ) * (-n - 1) + e = e + 2 * (-n - 1) by push_cast; ring,
    FL_shift, fzmul_val, mode_zmul, zero_add, mode_apply, show -(-n - 1) - 1 = n by ring]

omit hPos in
theorem YML_eq_mode (u : LatModuleGen L) (e p : ℤ) :
    YML L hEven hU u (2 * p + e) = mode (FL L hEven hU e u).1 p := by
  have h := mode_resc (YML L hEven hU u) 2 e p
  push_cast at h
  rw [← h, resc_YML]

omit hPos in
/-- **Lower truncation.** -/
theorem YML_truncation (u : LatModuleGen L) (x : MT L hEven hU) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → YML L hEven hU u k x = 0 := by
  obtain ⟨B0, h0⟩ := (FL L hEven hU 0 u).2 x
  obtain ⟨B1, h1⟩ := (FL L hEven hU 1 u).2 x
  refine ⟨2 * (B0.natAbs + B1.natAbs) + 2, fun k hk => ?_⟩
  obtain ⟨q, e, he, rfl⟩ : ∃ q e : ℤ, (e = 0 ∨ e = 1) ∧ k = 2 * q + e :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  rw [YML_eq_mode, mode_apply]
  rcases he with rfl | rfl
  · exact h0 _ (by omega)
  · exact h1 _ (by omega)

omit hPos in
/-- **The vacuum**: `Y^T(𝟙)₍k/2₎ = δ_{k,−2}`. -/
theorem YML_vacuum (k : ℤ) :
    YML L hEven hU (latVacuumGen L) k = if k = -2 then 1 else 0 := by
  rw [YML_apply, latVacuumGen, latStateGen, show (vacuumN (rank L)) = monomial 0 1 by
      rw [vacuumN, monomial_zero', map_one],
    FL_monomial_eGen, monoWordN_zero, Fw_nil]
  change mode (resc (YTL L hEven hU 0) 2 k) 0 = _
  rw [mode_resc, mul_zero, zero_add, YTL_zero]

/-- **The support condition** for `θ`: `Y^T(u)₍k/2₎ = 0` unless `k ≡ j (mod 2)`, `u ∈ 𝒱ʲ`. -/
theorem YML_support (j : ℕ) (u : LatModuleGen L)
    (hu : u ∈ (thetaAut L hEven hPos).twistedEigenspace 2 j) (k : ℤ)
    (hk : (k + j) % ((2 : ℕ) : ℤ) ≠ 0) : YML L hEven hU u k = 0 := by
  rw [Aut.twistedEigenspace, Module.End.mem_eigenspace_iff, HeisenbergN.exp_twisted_two] at hu
  have hu' : thetaLat L u = ((-1 : ℂ) ^ j) • u := hu
  have h := FL_theta L hEven hU hPos k u
  rw [hu', map_smul] at h
  have hsign : ((-1 : ℂ) ^ j) = -((-1 : ℂ) ^ k) := by
    rw [← zpow_natCast, neg_one_zpow_congr (b := k + 1) (by push_cast at hk ⊢; omega),
      zpow_add₀ (by norm_num), zpow_one, mul_neg_one]
  rw [hsign, neg_smul] at h
  have h2 : (2 * (-1 : ℂ) ^ k) • FL L hEven hU k u = 0 := by
    rw [mul_smul, two_smul, ← sub_eq_zero.mpr h.symm]
    abel
  have hne : (2 * (-1 : ℂ) ^ k) ≠ 0 := mul_ne_zero two_ne_zero (zpow_ne_zero _ (by norm_num))
  rw [YML_apply, (smul_eq_zero.mp h2).resolve_left hne]
  rfl

/-- **All rescaled twisted vertex operators are mutually local.** -/
theorem YML_local (u v : LatModuleGen L) (e e' : ℤ) :
    Local (resc (YML L hEven hU u) 2 e) (resc (YML L hEven hU v) 2 e') := by
  rw [resc_YML, resc_YML]
  exact FL_local L hEven hU hPos e e' u v

end Lattice

end VOA.Moonshine.LatticeTwisted
