/-
Ported from AxiomMath/CFSG (Apache-2.0), https://github.com/AxiomMath/CFSG,
commit 69cb972f587a3ecc035e092253167ff2e303c962 (source toolchain Lean
v4.35.0-rc3 with the module system), files:
  CFSG/Monster/CodeLattice.lean
  CFSG/Monster/CodeLatticeUnimodular.lean
  CFSG/Monster/Code/LatticeBasic.lean
  CFSG/Monster/Code/LatticeShort.lean
  CFSG/Monster/Code/LatticeCount.lean
  CFSG/Monster/SpinLattice/Lambda.lean
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
import VOA.Moonshine.MonsterGriess.Golay
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.Ring.RingNF

/-!
# Axiom's Monster port, part 2: the Leech lattice in code coordinates and `Λ/2Λ`

Second layer of the definitional closure of Axiom Math's `CFSG.Monster.Griess.AutO`:

* `codeLattice C` — the Leech lattice in the integer coordinates of Conway's construction scaled
  by `√8` (vectors `u` with `u ≡ m + 2·d (mod 4)`, `d ∈ C`, `m ∈ {0,1}`, `∑ uᵢ ≡ 4m (mod 8)`),
  with `codeLatticeSubgroup`;
* `codeLatticeModTwo C allOnes_mem_C = ModN (codeLatticeSubgroup _) 2`, i.e. `Λ/2Λ`, called `L2`;
* `minVecs` — the 196560 minimal vectors (`codeForm u u = 4`, i.e. `∑ uᵢ² = 32`), and
  `classOf : (Fin 24 → ℤ) → L2`;
* `lamVec`, `lamVecLin`, `lamCode`, `lamCodeCls` — the classes in `Λ/2Λ` attached to binary
  vectors and to codewords, used to build `phi0 : C × Cocode → Λ/2Λ` in `Short.lean`.

## Port notes
* Namespaces `CFSG.Monster`, `CFSG.Monster.Code`, `CFSG.Monster.SpinLattice` ↦
  `VOA.Moonshine.MonsterGriess`, `….Code`, `….SpinLattice`.
* Module-system syntax dropped.  Bodies verbatim.
* Omitted (not needed to state `AutO`): unimodularity of the code lattice, `hInt`, the quadratic
  form `qL`/`codeQuadForm`, lattice counting, `normSq`, and the `qL`/`polarBilin` evaluations of
  `lamVec`/`lamCodeCls`.
-/

namespace VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/CodeLattice.lean` -/
def bitLift (t : ZMod 2) : ℤ := t.val

theorem bitLift_zero_or_one (t : ZMod 2) : bitLift t = 0 ∨ bitLift t = 1 := by
  fin_cases t <;> decide

def weight (d : Fin 24 → ZMod 2) : ℤ := ∑ i, bitLift (d i)

def allOnes : Fin 24 → ZMod 2 := fun _ => 1

def codeLattice (C : Submodule (ZMod 2) (Fin 24 → ZMod 2)) : Set (Fin 24 → ℤ) :=
  {u | ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ d ∈ C,
    (∀ i, u i ≡ m + 2 * bitLift (d i) [ZMOD 4]) ∧ ∑ i, u i ≡ 4 * m [ZMOD 8]}

def codeForm (u v : Fin 24 → ℚ) : ℚ := (∑ i, u i * v i) / 8

theorem bitLift_add (a b : ZMod 2) : bitLift (a + b) = (bitLift a + bitLift b) % 2 := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitLift_add_one (a : ZMod 2) : bitLift (a + 1) = 1 - bitLift a := by
  fin_cases a <;> decide

theorem bitLift_one : bitLift 1 = 1 := rfl

variable {C : Submodule (ZMod 2) (Fin 24 → ZMod 2)}

theorem zero_mem_codeLattice : (0 : Fin 24 → ℤ) ∈ codeLattice C :=
  ⟨0, .inl rfl, 0, C.zero_mem, fun i => by simp [bitLift], by simp⟩

theorem add_mem_codeLattice (hΩ : allOnes ∈ C) {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C)
    (hv : v ∈ codeLattice C) : u + v ∈ codeLattice C := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  obtain ⟨m', hm', d', hd', hvd, hvs⟩ := hv
  have hsum : ∑ i, (u + v) i = ∑ i, u i + ∑ i, v i := by simp [Finset.sum_add_distrib]
  by_cases h2 : m = 1 ∧ m' = 1
  · obtain ⟨rfl, rfl⟩ := h2
    refine ⟨0, .inl rfl, d + d' + allOnes, C.add_mem (C.add_mem hd hd') hΩ, fun i => ?_, ?_⟩
    · have h1 := hud i
      have h1' := hvd i
      simp only [Pi.add_apply, allOnes, bitLift_add, bitLift_one]
      unfold Int.ModEq at h1 h1' ⊢
      have ha := bitLift_zero_or_one (d i)
      have hb := bitLift_zero_or_one (d' i)
      omega
    · rw [hsum]
      have h := hus.add hvs
      unfold Int.ModEq at h ⊢
      omega
  · refine ⟨m + m', ?_, d + d', C.add_mem hd hd', fun i => ?_, ?_⟩
    · omega
    · have h1 := hud i
      have h1' := hvd i
      simp only [Pi.add_apply, bitLift_add]
      unfold Int.ModEq at h1 h1' ⊢
      have ha := bitLift_zero_or_one (d i)
      have hb := bitLift_zero_or_one (d' i)
      omega
    · rw [hsum]
      have h := hus.add hvs
      unfold Int.ModEq at h ⊢
      omega

theorem neg_mem_codeLattice (hΩ : allOnes ∈ C) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    -u ∈ codeLattice C := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  have hsum : ∑ i, (-u) i = -∑ i, u i := by simp [Finset.sum_neg_distrib]
  rcases hm with rfl | rfl
  · refine ⟨0, .inl rfl, d, hd, fun i => ?_, ?_⟩
    · have h1 := hud i
      simp only [Pi.neg_apply]
      unfold Int.ModEq at h1 ⊢
      have ha := bitLift_zero_or_one (d i)
      omega
    · rw [hsum]
      unfold Int.ModEq at hus ⊢
      omega
  · refine ⟨1, .inr rfl, d + allOnes, C.add_mem hd hΩ, fun i => ?_, ?_⟩
    · have h1 := hud i
      simp only [Pi.neg_apply, Pi.add_apply, allOnes, bitLift_add_one]
      unfold Int.ModEq at h1 ⊢
      have ha := bitLift_zero_or_one (d i)
      omega
    · rw [hsum]
      unfold Int.ModEq at hus ⊢
      omega

def codeLatticeSubgroup (hΩ : allOnes ∈ C) : AddSubgroup (Fin 24 → ℤ) where
  carrier := codeLattice C
  zero_mem' := zero_mem_codeLattice
  add_mem' := add_mem_codeLattice hΩ
  neg_mem' := neg_mem_codeLattice hΩ

/-! ### From `CFSG/Monster/CodeLatticeUnimodular.lean` -/
variable (C) in
abbrev codeLatticeModTwo (hΩ : allOnes ∈ C) : Type := ModN (codeLatticeSubgroup hΩ) 2

theorem mem_two_range_iff (hΩ : allOnes ∈ C) (x : codeLatticeSubgroup hΩ) :
    x ∈ LinearMap.range (LinearMap.lsmul ℤ (codeLatticeSubgroup hΩ) ((2 : ℕ) : ℤ)) ↔
      ∃ w : codeLatticeSubgroup hΩ, (2 : ℤ) • (w : Fin 24 → ℤ) = x := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩

end VOA.Moonshine.MonsterGriess

namespace VOA.Moonshine.MonsterGriess.Code

open VOA.Moonshine.MonsterGriess

/-! ### From `CFSG/Monster/Code/LatticeBasic.lean` -/
theorem allOnes_mem_C : allOnes ∈ C := Ω_mem_C

theorem weight_eq_hammingNorm (d : Fin 24 → ZMod 2) : weight d = hammingNorm d := by
  rw [weight, hammingNorm_eq_sum_val]
  push_cast
  rfl

def liftℤ (d : Fin 24 → ZMod 2) : Fin 24 → ℤ := fun i => bitLift (d i)

theorem sum_liftℤ (d : Fin 24 → ZMod 2) : ∑ i, liftℤ d i = hammingNorm d := by
  rw [← weight_eq_hammingNorm]
  rfl

theorem sum_bitLift (d : Fin 24 → ZMod 2) : ∑ i, bitLift (d i) = hammingNorm d := sum_liftℤ d

theorem bitLift_cast (t : ZMod 2) : ((bitLift t : ℤ) : ZMod 2) = t := by
  rw [bitLift, Int.cast_natCast, ZMod.natCast_zmod_val]

/-! ### From `CFSG/Monster/Code/LatticeShort.lean` -/
def minVecs : Set (Fin 24 → ℤ) :=
  {u | u ∈ codeLattice C ∧ codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = 4}

/-! ### From `CFSG/Monster/Code/LatticeCount.lean` -/
noncomputable def classOf (u : Fin 24 → ℤ) : codeLatticeModTwo C allOnes_mem_C :=
  open Classical in
  if h : u ∈ codeLattice C then Submodule.Quotient.mk (⟨u, h⟩ : codeLatticeSubgroup allOnes_mem_C)
  else 0

end VOA.Moonshine.MonsterGriess.Code

namespace VOA.Moonshine.MonsterGriess.SpinLattice

open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Code

/-! ### From `CFSG/Monster/SpinLattice/Lambda.lean` -/
abbrev L2 : Type := codeLatticeModTwo C allOnes_mem_C

def cls (u : Fin 24 → ℤ) (hu : u ∈ codeLattice C) : L2 :=
  Submodule.Quotient.mk (⟨u, hu⟩ : codeLatticeSubgroup allOnes_mem_C)

theorem cls_add {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (hv : v ∈ codeLattice C) :
    cls u hu + cls v hv = cls (u + v) (add_mem_codeLattice allOnes_mem_C hu hv) := rfl

theorem cls_two_smul {w : Fin 24 → ℤ} (hw : w ∈ codeLattice C)
    (h : (2 : ℤ) • w ∈ codeLattice C) : cls ((2 : ℤ) • w) h = 0 := by
  rw [cls, Submodule.Quotient.mk_eq_zero, mem_two_range_iff]
  exact ⟨⟨w, hw⟩, rfl⟩

theorem cls_congr {u v : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (huv : u = v) :
    cls u hu = cls v (huv ▸ hu) := by
  subst huv; rfl

theorem bitLift_intCast (y : ℤ) : bitLift (y : ZMod 2) = y % 2 := by
  rw [bitLift, ZMod.val_intCast]
  omega

theorem mem_of_even {u y : Fin 24 → ℤ} (hu : ∀ i, u i = 2 * y i)
    (hy : (fun i => (y i : ZMod 2)) ∈ C) (hs : (∑ i, u i) % 8 = 0) : u ∈ codeLattice C := by
  refine ⟨0, .inl rfl, _, hy, fun i => ?_, ?_⟩
  · rw [hu i, bitLift_intCast]
    unfold Int.ModEq
    omega
  · unfold Int.ModEq
    omega

theorem bitLift_add' (x y : ZMod 2) :
    bitLift x + bitLift y = bitLift (x + y) + 2 * bitLift (x * y) := by
  fin_cases x <;> fin_cases y <;> rfl

theorem sum_affine (b c : Fin 24 → ℤ) (α β γ δ : ℤ) :
    ∑ k, (α + β * b k + γ * c k + δ * (b k * c k)) =
      24 * α + β * ∑ k, b k + γ * ∑ k, c k + δ * ∑ k, b k * c k := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

def lamSum (v : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun k => (hammingNorm v : ℤ) - 4 * bitLift (v k)

theorem lamSum_mem (v : Fin 24 → ZMod 2) : lamSum v ∈ codeLattice C := by
  set n : ℤ := ((hammingNorm v : ℕ) : ℤ)
  have hsum : ∑ k, lamSum v k = 20 * n := by
    simp only [lamSum, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bitLift, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  set m : ℤ := n % 2
  set t : ZMod 2 := ((n / 2 : ℤ) : ZMod 2)
  have hd : t • Ω ∈ C := C.smul_mem t Ω_mem_C
  refine ⟨m, by omega, t • Ω, hd, fun k => ?_, ?_⟩
  · simp only [lamSum, Pi.smul_apply, Ω, smul_eq_mul, mul_one, t, bitLift_intCast]
    unfold Int.ModEq
    have := bitLift_zero_or_one (v k)
    omega
  · rw [hsum]
    unfold Int.ModEq
    omega

def lamVec (v : Fin 24 → ZMod 2) : L2 := cls (lamSum v) (lamSum_mem v)

theorem lamSum_add (v w : Fin 24 → ZMod 2) :
    lamSum v + lamSum w = lamSum (v + w) + (2 : ℤ) • lamSum (v * w) := by
  funext k
  have h1 := hammingNorm_add_add v w
  have h2 := bitLift_add' (v k) (w k)
  simp only [lamSum, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have h1' : ((hammingNorm (v + w) : ℕ) : ℤ) + 2 * (hammingNorm (v * w) : ℕ) =
      (hammingNorm v : ℕ) + (hammingNorm w : ℕ) := by exact_mod_cast h1
  linear_combination h1'.symm - 4 * h2

theorem lamVec_add (v w : Fin 24 → ZMod 2) : lamVec (v + w) = lamVec v + lamVec w := by
  have h2 : (2 : ℤ) • lamSum (v * w) ∈ codeLattice C :=
    (codeLatticeSubgroup allOnes_mem_C).zsmul_mem (lamSum_mem _) 2
  calc lamVec (v + w)
        = cls (lamSum (v + w)) (lamSum_mem _) + cls ((2 : ℤ) • lamSum (v * w)) h2 := by
        rw [cls_two_smul (lamSum_mem _) h2, add_zero]
        rfl
    _ = cls (lamSum (v + w) + (2 : ℤ) • lamSum (v * w)) _ := cls_add _ _
    _ = cls (lamSum v + lamSum w) _ := cls_congr _ (lamSum_add v w).symm
    _ = lamVec v + lamVec w := (cls_add _ _).symm

theorem lamVec_zero : lamVec 0 = 0 := by
  have h := lamVec_add 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem lamVec_eq_zero_of_mem {c : Fin 24 → ZMod 2} (hc : c ∈ C) : lamVec c = 0 := by
  obtain ⟨s, hs⟩ := four_dvd_wt hc
  set w : Fin 24 → ℤ := fun k => 2 * (s : ℤ) - 2 * bitLift (c k) with hwdef
  have hw : w ∈ codeLattice C := by
    refine mem_of_even (y := fun k => (s : ℤ) - bitLift (c k)) (fun k => by simp only [hwdef]; ring)
      ?_ ?_
    · have : (fun k => (((s : ℤ) - bitLift (c k) : ℤ) : ZMod 2)) = (s : ZMod 2) • Ω + c := by
        funext k
        simp only [Int.cast_sub, Int.cast_natCast, Pi.add_apply, Pi.smul_apply, Ω, smul_eq_mul,
          mul_one, bitLift_cast]
        rw [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
      rw [this]
      exact C.add_mem (C.smul_mem _ Ω_mem_C) hc
    · simp only [hwdef, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bitLift, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs]
      push_cast
      omega
  have heq : lamSum c = (2 : ℤ) • w := by
    funext k
    simp only [lamSum, hwdef, Pi.smul_apply, smul_eq_mul, hs]
    push_cast
    ring
  rw [lamVec, cls_congr _ heq, cls_two_smul hw]

noncomputable def lamVecLin : (Fin 24 → ZMod 2) →ₗ[ZMod 2] L2 :=
  AddMonoidHom.toZModLinearMap 2
    { toFun := lamVec
      map_zero' := lamVec_zero
      map_add' := lamVec_add }

theorem lamVecLin_apply (v : Fin 24 → ZMod 2) : lamVecLin v = lamVec v := rfl

theorem le_ker_lamVecLin : C ≤ LinearMap.ker lamVecLin := fun _ hc => lamVec_eq_zero_of_mem hc

def Pint (a : Fin 24 → ZMod 2) : ℤ := bitLift (P a)

def lamCode (a : Fin 24 → ZMod 2) : Fin 24 → ℤ :=
  fun k => 2 * bitLift (a k) + 2 * Pint a - 4 * Pint a * bitLift (a k)

theorem lamCode_mem {a : Fin 24 → ZMod 2} (ha : a ∈ C) : lamCode a ∈ codeLattice C := by
  obtain ⟨s, hs⟩ := four_dvd_wt ha
  refine mem_of_even (y := fun k => bitLift (a k) + Pint a - 2 * Pint a * bitLift (a k))
    (fun k => by simp only [lamCode]; ring) ?_ ?_
  · have : (fun k => ((bitLift (a k) + Pint a - 2 * Pint a * bitLift (a k) : ℤ) : ZMod 2)) =
        a + (P a) • Ω := by
      funext k
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Pint, bitLift_cast, Pi.add_apply,
        Pi.smul_apply, Ω, smul_eq_mul, mul_one]
      rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul, zero_mul, sub_zero]
    rw [this]
    exact C.add_mem ha (C.smul_mem _ Ω_mem_C)
  · have e : ∑ k, lamCode a k = 2 * hammingNorm a + 48 * Pint a - 4 * Pint a * hammingNorm a := by
      have := sum_affine (fun k => bitLift (a k)) (fun k => bitLift (a k)) (2 * Pint a) 2
        (-4 * Pint a) 0
      simp only [sum_bitLift] at this
      rw [← sum_bitLift]
      simp only [lamCode]
      rw [show (∑ k, (2 * bitLift (a k) + 2 * Pint a - 4 * Pint a * bitLift (a k))) =
          ∑ k, (2 * Pint a + 2 * bitLift (a k) + -4 * Pint a * bitLift (a k) +
            0 * (bitLift (a k) * bitLift (a k))) from
        Finset.sum_congr rfl fun k _ => by ring, this, sum_bitLift]
      ring
    rw [e, hs]
    push_cast
    have h16 : 4 * Pint a * (4 * (s : ℤ)) = 8 * (2 * Pint a * s) := by ring
    omega

def lamCodeCls {a : Fin 24 → ZMod 2} (ha : a ∈ C) : L2 := cls (lamCode a) (lamCode_mem ha)

end VOA.Moonshine.MonsterGriess.SpinLattice
