/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean v4.35.0-rc3 with the
module system), files:
  CFSG/Monster/Griess/TrialityBasis/Labels.lean
  CFSG/Monster/SpinLattice/Isometry.lean (`XQ`, `DQ`, `XQ_eq`, `DQ_eq`, `lamT_zero`, `phi0_zero_left`)
  CFSG/Monster/SpinLattice/Lambda.lean (`lamSum_single`, `lamCode_of_P_zero`)
  CFSG/Monster/CodeLatticeUnimodular.lean (`two_bitLift_mem`)
Original authors (from the `@misc{axiom-cfsg}` citation, "Lean formalization of the
classification of finite simple groups", 2026):
  Cureton, Dean and Ilin, Vasily and Mehta, Bhavik and Voss, Niels and Cabral, Rafael and
  Defant, Colin and Gregory, Erik and Hill, Aaron and Hong, Letong and Hu, Qinheping and Jamner,
  Dustin and Jiang, Albert and Jordan, Tadeusz and Kurghinyan, Andranik and Lau, Kenny and
  Laurent, Jonathan and Liang, David and Limperg, Jannis and Mahns, Simon and Nugent, Brian and
  Olson, Connor and Ono, Ken and Paul, Eric and Rajan, Dhruv and Ram, Karun and Ray, Charlie and
  Siu, Ho Chung and Swaminathan, Ashvin A. and Thorner, Jesse and Tsaplin, Aleksey and Wang,
  Chenkai.
Port to Lean 4.30.0 / Mathlib v4.30.0 for LeanVOA by Fedor K. Popov (with Claude).
Released under the Apache 2.0 license.  Modifications relative to the source are listed in the
"Port notes" section of the module docstring below.
-/
import VOA.Moonshine.MonsterGriess.OctadEvenSubset
import VOA.Moonshine.MonsterGriess.LatticeFamilies

/-!
# Axiom's Monster port (triality basis, part 1): the short-vector labels `rMinus`, `rPlus`, `rOdd`, `rOct`

The 98280 short classes of `Q/Z(Q) ≅ Λ/2Λ` are labelled by four explicit families of elements of
the extraspecial group `Q`:

* `rMinus i j = DQ (δ_{ij})`, `rPlus i j = XQ (Ω, 0) · DQ (δ_{ij})` (the classes of
  `4e_i ∓ 4e_j`);
* `rOdd c i = XQ (c + m Ω, 0) · DQ (e_i)` (the classes of the odd vectors `oddMin i c`);
* `rOct d δ = XQ (d + n Ω, 0) · DQ (δ)` (the classes of `2·d - 4·δ` for an octad `d` and an even
  subset `δ ⊆ d`).

For each family: the `Q`-coordinates (`coordOf_*`, `centralCoord_* = 0`) and the identification
`phi0 (coordOf r) = classOf v` with the corresponding minimal vector `v` (`phi0_coordOf_rMinus`,
`phi0_coordOf_rPlus`, `phi0_coordOf_rOdd`, `phi0_coordOf_rOct`), and `rOct_compl`
(`δ` and `d \ δ` give the same element).

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.SpinLattice`, `CFSG.Monster.Griess` ↦
  `VOA.Moonshine.MonsterGriess`, `….SpinLattice`, `VOA.Moonshine.MonsterGriess` (as in the earlier
  ports).  Module-system syntax, `@[expose]` and the source's `attribute [-instance] …` line
  dropped.  Bodies verbatim except as listed.
* Small pieces of other source files, not ported earlier, are added at the top: `two_bitLift_mem`
  (`CodeLatticeUnimodular.lean`), `XQ`, `DQ`, `XQ_eq`, `DQ_eq`, `lamT_zero`, `phi0_zero_left`
  (`SpinLattice/Isometry.lean`; `lamT_zero` through our `lamTHom` of `LatticeQuadratic.lean`),
  `lamSum_single`, `lamCode_of_P_zero` (`SpinLattice/Lambda.lean`).
* **Renamed:** the source's `CFSG.Monster.Griess.lamCode_Ω` (`lamCode Ω = twoΩ`) ↦
  `lamCode_Ω_eq_twoΩ`, because `VOA.Moonshine.GriessDictionary.lamCode_Ω` (a different
  statement) exists in `MoonshineCNGriessFrameBlock.lean`, which opens this namespace.
* Drift: `dite_eq_left hu` (absent in Mathlib v4.30) ↦ `dif_pos hu` (`classOf_eq_cls`).
-/

set_option linter.style.longLine false
set_option linter.style.show false

/-! ### From `CFSG/Monster/CodeLatticeUnimodular.lean` -/

namespace VOA.Moonshine.MonsterGriess

variable {C : Submodule (ZMod 2) (Fin 24 → ZMod 2)}

theorem two_bitLift_mem (hC4 : ∀ d ∈ C, weight d % 4 = 0) {d : Fin 24 → ZMod 2} (hd : d ∈ C) :
    (fun i => 2 * bitLift (d i)) ∈ codeLattice C := by
  refine ⟨0, .inl rfl, d, hd, fun i => by simp, ?_⟩
  have h := hC4 d hd
  simp only [← Finset.mul_sum, mul_zero]
  unfold Int.ModEq
  unfold weight at h
  omega

end VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/SpinLattice/Isometry.lean` and `CFSG/Monster/SpinLattice/Lambda.lean` -/

namespace VOA.Moonshine.MonsterGriess.SpinLattice

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin

noncomputable def XQ (e : Parker) : Q := ⟨XU e, XU_mem_Q e⟩

noncomputable def DQ (δ : Cocode) : Q := ⟨DU δ, DU_mem_Q δ⟩

theorem XQ_eq (e : Parker) : XQ e = spinEquiv ⟨e.sign, e.code, thetaD e.code⟩ :=
  Subtype.ext (XU_eq_toGL e)

theorem DQ_eq (δ : Cocode) : DQ δ = spinEquiv ⟨0, 0, δ⟩ := Subtype.ext (DU_eq_toGL δ)

theorem lamT_zero : lamT 0 = 0 := lamTHom.map_zero

theorem phi0_zero_left (δ : Cocode) : phi0 (0, δ) = lamCocode δ := by
  rw [phi0_apply, lamT_zero, zero_add]

theorem lamSum_single (i : Fin 24) :
    lamSum (Pi.single i 1) = fun k => 1 - 4 * (Pi.single i (1 : ℤ) : Fin 24 → ℤ) k := by
  funext k
  have h1 : hammingNorm (Pi.single i (1 : ZMod 2) : Fin 24 → ZMod 2) = 1 := by
    rw [hammingNorm, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    by_cases hj : j = i <;> simp [hj]
  simp only [lamSum, h1]
  by_cases hk : k = i
  · subst hk; simp; rfl
  · simp [hk, bitLift]

theorem lamCode_of_P_zero {a : Fin 24 → ZMod 2} (h : P a = 0) :
    lamCode a = fun k => 2 * bitLift (a k) := by
  funext k; simp [lamCode, Pint, h, bitLift]

end VOA.Moonshine.MonsterGriess.SpinLattice

/-! ### From `CFSG/Monster/Griess/TrialityBasis/Labels.lean` -/

namespace VOA.Moonshine.MonsterGriess

open VOA.Moonshine.MonsterGriess.Code VOA.Moonshine.MonsterGriess.Spin
  VOA.Moonshine.MonsterGriess.SpinLattice

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem XQ_mul_DQ (e : Parker) (δ : Cocode) :
    XQ e * DQ δ = spinEquiv ⟨e.sign, e.code, thetaD e.code + δ⟩ := Subtype.ext (XU_mul_DU e δ)

theorem coordOf_spinEquiv (x : SpinCoord) : coordOf (spinEquiv x) = (x.a, x.δ) :=
  congrArg (fun y : SpinCoord => (y.a, y.δ)) (spinEquiv.symm_apply_apply x)

theorem centralCoord_spinEquiv (x : SpinCoord) : centralCoord (spinEquiv x) = x.s :=
  congrArg SpinCoord.s (spinEquiv.symm_apply_apply x)

theorem phi0_thetaD_add (a : C) (ε : Cocode) :
    phi0 (a, thetaD a + ε) = lamX a + lamCocode ε := by
  rw [phi0_apply, lamT, map_add]
  have h : lamCocode (thetaD a) + lamCocode (thetaD a) = 0 := by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  calc lamX a + lamCocode (thetaD a) + (lamCocode (thetaD a) + lamCocode ε)
      = lamX a + (lamCocode (thetaD a) + lamCocode (thetaD a)) + lamCocode ε := by abel
    _ = lamX a + lamCocode ε := by rw [h, add_zero]

theorem classOf_eq_cls {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) : classOf u = cls u hu := by
  unfold classOf
  exact dif_pos hu

theorem cls_eq_of_eq_add {x u w : Fin 24 → ℤ} (hx : x ∈ codeLattice C) (hu : u ∈ codeLattice C)
    (hw : w ∈ codeLattice C) (h : x = u + (2 : ℤ) • w) : cls x hx = cls u hu := by
  have h2 : (2 : ℤ) • w ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hw 2
  rw [cls_congr hx h, ← cls_add hu h2, cls_two_smul hw h2, add_zero]

theorem mem_L_sub {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    u - v ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).sub_mem hu hv

theorem mem_L_add {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    u + v ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).add_mem hu hv

theorem mem_L_zsmul {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (n : ℤ) :
    n • u ∈ codeLattice C := (codeLatticeSubgroup allOnes_mem_C).zsmul_mem hu n

def lamI (i : Fin 24) : Fin 24 → ℤ :=
  fun k => 1 - 4 * (Pi.single i (1 : ℤ) : Fin 24 → ℤ) k

theorem lamSum_single' (i : Fin 24) : lamSum (Pi.single i 1) = lamI i := lamSum_single i

theorem lamI_mem (i : Fin 24) : lamI i ∈ codeLattice C := lamSum_single' i ▸ lamSum_mem _

def twoΩ : Fin 24 → ℤ := fun _ => 2

theorem twoΩ_mem : twoΩ ∈ codeLattice C := by
  have h := two_bitLift_mem weight_mod_four' Ω_mem_C
  have e : (fun i => 2 * bitLift (Ω i)) = twoΩ := funext fun _ => rfl
  rwa [e] at h

def twoLift (d : Fin 24 → ZMod 2) : Fin 24 → ℤ := fun k => 2 * bitLift (d k)

theorem twoLift_mem {d : Fin 24 → ZMod 2} (hd : d ∈ C) : twoLift d ∈ codeLattice C :=
  two_bitLift_mem weight_mod_four' hd

def vMinus (i j : Fin 24) : Fin 24 → ℤ := (4 : ℤ) • eℤ i - (4 : ℤ) • eℤ j

def vPlus (i j : Fin 24) : Fin 24 → ℤ := (4 : ℤ) • eℤ i + (4 : ℤ) • eℤ j

def vOct (d : Fin 24 → ZMod 2) (δ : Finset (Fin 24)) : Fin 24 → ℤ :=
  (2 : ℤ) • liftℤ d - (4 : ℤ) • liftℤ (Octad.ind δ)

theorem K_Ω_right {x : Fin 24 → ZMod 2} (hx : x ∈ C) : K x Ω = 0 := by
  have h : x * Ω = x := by
    funext i
    simp [Ω]
  rw [K_eq, h]
  obtain ⟨m, hm⟩ := four_dvd_wt hx
  rw [hm, show 4 * m / 2 = 2 * m by omega, Nat.cast_mul, Nat.cast_ofNat,
    show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem P_add_smul_Ω {x : Fin 24 → ZMod 2} (hx : x ∈ C) (m : ZMod 2) : P (x + m • Ω) = P x := by
  rcases zmod2_cases m with rfl | rfl
  · rw [zero_smul, add_zero]
  · rw [one_smul, P_add hx Ω_mem_C, P_Ω, K_Ω_right hx, add_zero, add_zero]

def deltaPair (i j : Fin 24) : Cocode :=
  Submodule.Quotient.mk (Pi.single i 1 + Pi.single j 1)

noncomputable def rMinus (i j : Fin 24) : Q := DQ (deltaPair i j)

noncomputable def rPlus (i j : Fin 24) : Q := XQ ⟨ΩC, 0⟩ * DQ (deltaPair i j)

def mOdd (c : C₀) (i : Fin 24) : ZMod 2 :=
  ((c : C) : Fin 24 → ZMod 2) i + P ((c : C) : Fin 24 → ZMod 2)

def aOdd (c : C₀) (i : Fin 24) : C := (c : C) + mOdd c i • ΩC

noncomputable def rOdd (c : C₀) (i : Fin 24) : Q :=
  XQ ⟨aOdd c i, 0⟩ * DQ (Submodule.Quotient.mk (Pi.single i 1))

def nOct (δ : Finset (Fin 24)) : ZMod 2 := ((δ.card / 2 : ℕ) : ZMod 2)

def aOct (d : C) (δ : Finset (Fin 24)) : C := d + nOct δ • ΩC

noncomputable def rOct (d : C) (δ : Finset (Fin 24)) : Q :=
  XQ ⟨aOct d δ, 0⟩ * DQ (Submodule.Quotient.mk (Octad.ind δ))

theorem rMinus_eq (i j : Fin 24) : rMinus i j = spinEquiv ⟨0, 0, deltaPair i j⟩ := DQ_eq _

theorem rPlus_eq (i j : Fin 24) :
    rPlus i j = spinEquiv ⟨0, ΩC, thetaD ΩC + deltaPair i j⟩ := XQ_mul_DQ _ _

theorem rOdd_eq (c : C₀) (i : Fin 24) :
    rOdd c i = spinEquiv ⟨0, aOdd c i, thetaD (aOdd c i) +
      Submodule.Quotient.mk (Pi.single i 1)⟩ := XQ_mul_DQ _ _

theorem rOct_eq (d : C) (δ : Finset (Fin 24)) :
    rOct d δ = spinEquiv ⟨0, aOct d δ, thetaD (aOct d δ) +
      Submodule.Quotient.mk (Octad.ind δ)⟩ := XQ_mul_DQ _ _

theorem coordOf_rMinus (i j : Fin 24) : coordOf (rMinus i j) = (0, deltaPair i j) :=
  (congrArg coordOf (rMinus_eq i j)).trans (coordOf_spinEquiv _)

theorem coordOf_rPlus (i j : Fin 24) : coordOf (rPlus i j) = (ΩC, thetaD ΩC + deltaPair i j) :=
  (congrArg coordOf (rPlus_eq i j)).trans (coordOf_spinEquiv _)

theorem coordOf_rOdd (c : C₀) (i : Fin 24) :
    coordOf (rOdd c i) = (aOdd c i, thetaD (aOdd c i) + Submodule.Quotient.mk (Pi.single i 1)) :=
  (congrArg coordOf (rOdd_eq c i)).trans (coordOf_spinEquiv _)

theorem coordOf_rOct (d : C) (δ : Finset (Fin 24)) :
    coordOf (rOct d δ) = (aOct d δ, thetaD (aOct d δ) + Submodule.Quotient.mk (Octad.ind δ)) :=
  (congrArg coordOf (rOct_eq d δ)).trans (coordOf_spinEquiv _)

theorem centralCoord_rMinus (i j : Fin 24) : centralCoord (rMinus i j) = 0 :=
  (congrArg centralCoord (rMinus_eq i j)).trans (centralCoord_spinEquiv _)

theorem centralCoord_rPlus (i j : Fin 24) : centralCoord (rPlus i j) = 0 :=
  (congrArg centralCoord (rPlus_eq i j)).trans (centralCoord_spinEquiv _)

theorem centralCoord_rOdd (c : C₀) (i : Fin 24) : centralCoord (rOdd c i) = 0 :=
  (congrArg centralCoord (rOdd_eq c i)).trans (centralCoord_spinEquiv _)

theorem centralCoord_rOct (d : C) (δ : Finset (Fin 24)) : centralCoord (rOct d δ) = 0 :=
  (congrArg centralCoord (rOct_eq d δ)).trans (centralCoord_spinEquiv _)

theorem single_mul_single {i j : Fin 24} (hij : i ≠ j) :
    (Pi.single i 1 : Fin 24 → ZMod 2) * Pi.single j 1 = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [hij]
  · simp [hk]

theorem lamSum_zero : lamSum 0 = 0 := by
  funext k
  simp [lamSum, bitLift]

theorem lamSum_pair {i j : Fin 24} (hij : i ≠ j) :
    lamSum (Pi.single i 1 + Pi.single j 1) = lamI i + lamI j := by
  have h := lamSum_add (Pi.single i 1) (Pi.single j 1)
  rw [single_mul_single hij, lamSum_zero, smul_zero, add_zero, lamSum_single',
    lamSum_single'] at h
  exact h.symm

theorem lamSum_pair_eq_vMinus {i j : Fin 24} (hij : i ≠ j) :
    lamSum (Pi.single i 1 + Pi.single j 1) = vMinus i j + (2 : ℤ) • lamI i := by
  rw [lamSum_pair hij]
  funext k
  simp only [lamI, vMinus, eℤ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem lamCode_Ω_eq_twoΩ : lamCode Ω = twoΩ := by
  rw [lamCode_of_P_zero P_Ω]
  rfl

theorem lamCode_Ω_add_lamSum_pair {i j : Fin 24} (hij : i ≠ j) :
    lamCode Ω + lamSum (Pi.single i 1 + Pi.single j 1) =
      vPlus i j + (2 : ℤ) • (lamI i + lamI j) := by
  rw [lamSum_pair hij, lamCode_Ω_eq_twoΩ]
  funext k
  simp only [lamI, vPlus, twoΩ, eℤ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

def wOdd (c : C₀) (i : Fin 24) : Fin 24 → ℤ :=
  if ((c : C) : Fin 24 → ZMod 2) i = 0 then twoLift ((c : C) : Fin 24 → ZMod 2) else lamI i

theorem wOdd_mem (c : C₀) (i : Fin 24) : wOdd c i ∈ codeLattice C := by
  unfold wOdd
  split
  · exact twoLift_mem (c : C).2
  · exact lamI_mem i

private theorem odd_key₀ : ∀ x xi p : ZMod 2,
    2 * bitLift (x + (xi + p)) + 2 * bitLift p - 4 * bitLift p * bitLift (x + (xi + p)) +
        (1 - 4 * 0) =
      (-1) ^ x.val * (1 - 4 * 0) + 2 * (if xi = 0 then 2 * bitLift x else 1 - 4 * 0) := by
  decide

private theorem odd_key₁ : ∀ x p : ZMod 2,
    2 * bitLift (x + (x + p)) + 2 * bitLift p - 4 * bitLift p * bitLift (x + (x + p)) +
        (1 - 4 * 1) =
      (-1) ^ x.val * (1 - 4 * 1) + 2 * (if x = 0 then 2 * bitLift x else 1 - 4 * 1) := by
  decide

theorem coe_aOdd (c : C₀) (i : Fin 24) :
    ((aOdd c i : C) : Fin 24 → ZMod 2) = ((c : C) : Fin 24 → ZMod 2) + mOdd c i • Ω := rfl

theorem P_aOdd (c : C₀) (i : Fin 24) :
    P ((aOdd c i : C) : Fin 24 → ZMod 2) = P ((c : C) : Fin 24 → ZMod 2) := by
  rw [coe_aOdd]
  exact P_add_smul_Ω (c : C).2 _

theorem lamCode_aOdd_add (c : C₀) (i : Fin 24) :
    lamCode ((aOdd c i : C) : Fin 24 → ZMod 2) + lamSum (Pi.single i 1) =
      oddMin i ((c : C) : Fin 24 → ZMod 2) + (2 : ℤ) • wOdd c i := by
  funext k
  have hak : ((aOdd c i : C) : Fin 24 → ZMod 2) k = ((c : C) : Fin 24 → ZMod 2) k +
      (((c : C) : Fin 24 → ZMod 2) i + P ((c : C) : Fin 24 → ZMod 2)) := by
    rw [coe_aOdd]
    simp [mOdd, Ω]
  have hw : wOdd c i k = if ((c : C) : Fin 24 → ZMod 2) i = 0 then
      2 * bitLift (((c : C) : Fin 24 → ZMod 2) k)
    else 1 - 4 * (Pi.single i (1 : ℤ) : Fin 24 → ℤ) k := by
    unfold wOdd
    split_ifs <;> rfl
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, lamSum_single', smul_eq_mul, hw]
  simp only [lamCode, Pint, P_aOdd, hak, oddMin, lamI]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, ite_true]
    have := odd_key₁ (((c : C) : Fin 24 → ZMod 2) k) (P ((c : C) : Fin 24 → ZMod 2))
    split_ifs at this ⊢ <;> linarith
  · simp only [Pi.single_eq_of_ne hk, hk, ite_false]
    have := odd_key₀ (((c : C) : Fin 24 → ZMod 2) k) (((c : C) : Fin 24 → ZMod 2) i)
      (P ((c : C) : Fin 24 → ZMod 2))
    split_ifs at this ⊢ <;> linarith

def wOct (d : Fin 24 → ZMod 2) (δ : Finset (Fin 24)) : Fin 24 → ℤ :=
  fun k => ((δ.card / 2 : ℕ) : ℤ) + bitLift (nOct δ) - 2 * bitLift (nOct δ) * bitLift (d k)

theorem bitLift_nOct (δ : Finset (Fin 24)) : bitLift (nOct δ) = ((δ.card / 2 % 2 : ℕ) : ℤ) := by
  rw [bitLift, nOct, ZMod.val_natCast]

theorem wOct_eq (d : Fin 24 → ZMod 2) (δ : Finset (Fin 24)) :
    wOct d δ = (((δ.card / 2 + δ.card / 2 % 2) / 2 : ℕ) : ℤ) • twoΩ -
      bitLift (nOct δ) • twoLift d := by
  funext k
  simp only [wOct, twoΩ, twoLift, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bitLift_nOct]
  have h : (((δ.card / 2 + δ.card / 2 % 2) / 2 : ℕ) : ℤ) * 2 =
      ((δ.card / 2 : ℕ) : ℤ) + ((δ.card / 2 % 2 : ℕ) : ℤ) := by
    have : (δ.card / 2 + δ.card / 2 % 2) / 2 * 2 = δ.card / 2 + δ.card / 2 % 2 := by omega
    exact_mod_cast this
  linear_combination -h

theorem wOct_mem {d : Fin 24 → ZMod 2} (hd : d ∈ C) (δ : Finset (Fin 24)) :
    wOct d δ ∈ codeLattice C := by
  rw [wOct_eq]
  exact mem_L_sub (mem_L_zsmul twoΩ_mem _) (mem_L_zsmul (twoLift_mem hd) _)

theorem hammingNorm_ind (δ : Finset (Fin 24)) : hammingNorm (Octad.ind δ) = δ.card := by
  rw [← card_supp]
  congr 1
  ext k
  simp [supp, Octad.ind]

private theorem oct_key : ∀ x n : ZMod 2,
    2 * bitLift (x + n) = 2 * bitLift x + 2 * bitLift n - 4 * bitLift n * bitLift x := by
  decide

theorem coe_aOct (d : C) (δ : Finset (Fin 24)) :
    ((aOct d δ : C) : Fin 24 → ZMod 2) = (d : Fin 24 → ZMod 2) + nOct δ • Ω := rfl

theorem lamCode_aOct_add {d : C} (hP : P (d : Fin 24 → ZMod 2) = 0) {δ : Finset (Fin 24)}
    (he : Even δ.card) :
    lamCode ((aOct d δ : C) : Fin 24 → ZMod 2) + lamSum (Octad.ind δ) =
      vOct d δ + (2 : ℤ) • wOct d δ := by
  have hPa : P ((aOct d δ : C) : Fin 24 → ZMod 2) = 0 := by
    rw [coe_aOct, P_add_smul_Ω d.2, hP]
  rw [lamCode_of_P_zero hPa]
  funext k
  have hak : ((aOct d δ : C) : Fin 24 → ZMod 2) k = (d : Fin 24 → ZMod 2) k + nOct δ := by
    rw [coe_aOct]
    simp [Ω]
  obtain ⟨s, hs⟩ := he
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lamSum, hammingNorm_ind,
    vOct, wOct, liftℤ, hak]
  have h := oct_key ((d : Fin 24 → ZMod 2) k) (nOct δ)
  have hs' : ((δ.card : ℕ) : ℤ) = 2 * ((δ.card / 2 : ℕ) : ℤ) := by
    rw [hs]
    push_cast
    omega
  rw [hs']
  linarith

theorem fam₁Param_ne_zero_iff' {p : (Fin 24 × Fin 24) × (Bool × Bool)} (hp : p.1.1 < p.1.2)
    (k : Fin 24) : fam₁Param p k ≠ 0 ↔ k = p.1.1 ∨ k = p.1.2 := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp
  have h1 := sgn_ne_zero p.2.1
  have h2 := sgn_ne_zero p.2.2
  by_cases hk1 : k = p.1.1
  · subst hk1
    simp only [fam₁Param, ite_true, hne, ite_false, add_zero, true_or, iff_true]
    exact mul_ne_zero (by norm_num) h1
  · by_cases hk2 : k = p.1.2
    · subst hk2
      simp only [fam₁Param, hk1, ite_false, ite_true, zero_add, or_true, iff_true]
      exact mul_ne_zero (by norm_num) h2
    · simp [fam₁Param, hk1, hk2]

theorem fam₁Param_mem {p : (Fin 24 × Fin 24) × (Bool × Bool)} (hp : p.1.1 < p.1.2) :
    fam₁Param p ∈ minFamily₁ := by
  refine ⟨?_, fun k hk => ?_⟩
  · have : (Finset.univ.filter fun k => fam₁Param p k ≠ 0) = {p.1.1, p.1.2} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact fam₁Param_ne_zero_iff' hp k
    rw [this, Finset.card_pair (ne_of_lt hp)]
  · have hne : p.1.1 ≠ p.1.2 := ne_of_lt hp
    rcases (fam₁Param_ne_zero_iff' hp k).1 hk with rfl | rfl
    · simp only [fam₁Param, ite_true, hne, ite_false, add_zero, Code.sgn]
      split_ifs <;> norm_num
    · simp only [fam₁Param, Ne.symm hne, ite_false, ite_true, zero_add, Code.sgn]
      split_ifs <;> norm_num

theorem vMinus_eq_fam₁Param (i j : Fin 24) :
    vMinus i j = fam₁Param ((i, j), (false, true)) := by
  funext k
  simp only [vMinus, fam₁Param, eℤ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Code.sgn]
  split_ifs <;> simp_all

theorem neg_vMinus_eq_fam₁Param (i j : Fin 24) :
    -vMinus i j = fam₁Param ((i, j), (true, false)) := by
  funext k
  simp only [vMinus, fam₁Param, eℤ, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Code.sgn]
  split_ifs <;> simp_all

theorem vPlus_eq_fam₁Param (i j : Fin 24) :
    vPlus i j = fam₁Param ((i, j), (false, false)) := by
  funext k
  simp only [vPlus, fam₁Param, eℤ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    Code.sgn]
  split_ifs <;> simp_all

theorem neg_vPlus_eq_fam₁Param (i j : Fin 24) :
    -vPlus i j = fam₁Param ((i, j), (true, true)) := by
  funext k
  simp only [vPlus, fam₁Param, eℤ, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Code.sgn]
  split_ifs <;> simp_all

theorem vMinus_mem {i j : Fin 24} (hij : i < j) : vMinus i j ∈ minVecs := by
  rw [vMinus_eq_fam₁Param i j]
  exact minFamily₁_subset (fam₁Param_mem hij)

theorem vPlus_mem {i j : Fin 24} (hij : i < j) : vPlus i j ∈ minVecs := by
  rw [vPlus_eq_fam₁Param i j]
  exact minFamily₁_subset (fam₁Param_mem hij)

theorem oddMin_mem (c : C₀) (i : Fin 24) : oddMin i ((c : C) : Fin 24 → ZMod 2) ∈ minVecs :=
  minFamily₃_subset ⟨i, _, (c : C).2, rfl⟩

theorem mem_supp_iff {d : Fin 24 → ZMod 2} {k : Fin 24} : k ∈ supp d ↔ d k ≠ 0 := by
  simp [supp]

theorem vOct_eq_fam₂Vec {d : Fin 24 → ZMod 2} {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) :
    vOct d δ = fam₂Vec d δ := by
  funext k
  simp only [vOct, fam₂Vec, liftℤ, Octad.ind, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rcases zmod2_cases (d k) with h | h
  · have hk : k ∉ δ := fun hk => (mem_supp_iff.1 (hδ hk)) h
    simp [h, hk, bitLift]
  · rw [h]
    by_cases hk : k ∈ δ
    · simp [hk]
      rfl
    · simp [hk]
      rfl

theorem fam₂Vec_mem {d : Fin 24 → ZMod 2} (hd : d ∈ C) (hw : hammingNorm d = 8)
    {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) (he : Even δ.card) : fam₂Vec d δ ∈ minFamily₂ := by
  refine ⟨d, hd, hw, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · simp only [fam₂Vec, hi, ite_false]
    split_ifs <;> norm_num
  · simp [fam₂Vec, hi]
  · have : (Finset.univ.filter fun i => fam₂Vec d δ i = -2) = δ := by
      ext i
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and]
      constructor
      · intro h
        by_contra hiT
        simp only [fam₂Vec, hiT, ite_false] at h
        split_ifs at h
      · intro hi
        have hdi : d i ≠ 0 := mem_supp_iff.1 (hδ hi)
        simp [fam₂Vec, hdi, hi]
    rw [this]
    exact he

theorem vOct_mem {d : Fin 24 → ZMod 2} (hd : d ∈ C) (hw : hammingNorm d = 8)
    {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) (he : Even δ.card) : vOct d δ ∈ minVecs := by
  rw [vOct_eq_fam₂Vec hδ]
  exact minFamily₂_subset (fam₂Vec_mem hd hw hδ he)

theorem lamX_add_lamCocode (a : C) (v : Fin 24 → ZMod 2) :
    lamX a + lamCocode (Submodule.Quotient.mk v) =
      cls (lamCode (a : Fin 24 → ZMod 2) + lamSum v)
        (mem_L_add (lamCode_mem a.2) (lamSum_mem v)) := cls_add _ _

theorem phi0_coordOf_rMinus {i j : Fin 24} (hij : i < j) :
    phi0 (coordOf (rMinus i j)) = classOf (vMinus i j) := by
  refine (congrArg phi0 (coordOf_rMinus i j)).trans ?_
  have hv := (vMinus_mem hij).1
  rw [phi0_zero_left, deltaPair, lamCocode_mk, lamVec, classOf_eq_cls hv]
  exact cls_eq_of_eq_add _ hv (lamI_mem i) (lamSum_pair_eq_vMinus hij.ne)

theorem phi0_coordOf_rPlus {i j : Fin 24} (hij : i < j) :
    phi0 (coordOf (rPlus i j)) = classOf (vPlus i j) := by
  refine (congrArg phi0 (coordOf_rPlus i j)).trans ?_
  have hv := (vPlus_mem hij).1
  rw [phi0_thetaD_add, deltaPair, lamX_add_lamCocode, classOf_eq_cls hv]
  exact cls_eq_of_eq_add _ hv (mem_L_add (lamI_mem i) (lamI_mem j))
    (lamCode_Ω_add_lamSum_pair hij.ne)

theorem phi0_coordOf_rOdd (c : C₀) (i : Fin 24) :
    phi0 (coordOf (rOdd c i)) = classOf (oddMin i ((c : C) : Fin 24 → ZMod 2)) := by
  refine (congrArg phi0 (coordOf_rOdd c i)).trans ?_
  have hv := (oddMin_mem c i).1
  rw [phi0_thetaD_add, lamX_add_lamCocode, classOf_eq_cls hv]
  exact cls_eq_of_eq_add _ hv (wOdd_mem c i) (lamCode_aOdd_add c i)

theorem P_octad {d : Fin 24 → ZMod 2} (hw : hammingNorm d = 8) : P d = 0 := by
  rw [P, hw]
  rfl

theorem phi0_coordOf_rOct {d : C} (hw : hammingNorm (d : Fin 24 → ZMod 2) = 8)
    {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) (he : Even δ.card) :
    phi0 (coordOf (rOct d δ)) = classOf (vOct d δ) := by
  refine (congrArg phi0 (coordOf_rOct d δ)).trans ?_
  have hv := (vOct_mem d.2 hw hδ he).1
  rw [phi0_thetaD_add, lamX_add_lamCocode, classOf_eq_cls hv]
  exact cls_eq_of_eq_add _ hv (wOct_mem d.2 δ) (lamCode_aOct_add (P_octad hw) he)

theorem nOct_compl {d : Finset (Fin 24)} (hd : d.card = 8) {δ : Finset (Fin 24)} (hδ : δ ⊆ d)
    (he : Even δ.card) : nOct (d \ δ) = nOct δ := by
  unfold nOct
  rw [Finset.card_sdiff_of_subset hδ, hd, ZMod.natCast_eq_natCast_iff']
  obtain ⟨s, hs⟩ := he
  have : δ.card ≤ 8 := hd ▸ Finset.card_le_card hδ
  omega

theorem ind_compl_supp {d : Fin 24 → ZMod 2} {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) :
    Octad.ind (supp d \ δ) = Octad.ind δ + d := by
  funext k
  simp only [Octad.ind, Pi.add_apply, Finset.mem_sdiff]
  by_cases hk : k ∈ supp d
  · have hdk : d k = 1 := by
      rcases zmod2_cases (d k) with h | h
      · exact absurd h (mem_supp_iff.1 hk)
      · exact h
    by_cases hkδ : k ∈ δ
    · simp only [hk, hkδ, not_true_eq_false, and_false, ite_false, ite_true, hdk]
      decide
    · simp [hk, hkδ, hdk]
  · have hdk : d k = 0 := by
      by_contra h
      exact hk (mem_supp_iff.2 h)
    have hkδ : k ∉ δ := fun h => hk (hδ h)
    simp [hk, hkδ, hdk]

theorem mk_ind_compl {d : C} {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) :
    (Submodule.Quotient.mk (Octad.ind (supp d \ δ)) : Cocode) =
      Submodule.Quotient.mk (Octad.ind δ) := by
  rw [ind_compl_supp hδ, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero C).2 d.2,
    add_zero]

theorem rOct_compl {d : C} (hw : hammingNorm (d : Fin 24 → ZMod 2) = 8) {δ : Finset (Fin 24)}
    (hδ : δ ⊆ supp d) (he : Even δ.card) : rOct d (supp d \ δ) = rOct d δ :=
  congrArg₂ (fun (n : ZMod 2) (ε : Cocode) => XQ ⟨d + n • ΩC, 0⟩ * DQ ε)
    (nOct_compl (by rw [card_supp, hw]) hδ he) (mk_ind_compl hδ)

end VOA.Moonshine.MonsterGriess
