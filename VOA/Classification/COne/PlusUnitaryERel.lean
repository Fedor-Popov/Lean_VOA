/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryCharged
import VOA.Classification.COne.PlusUnitaryReduce

/-!
# H2: the `E`-relation in Zhu's algebra of `V_{2m}⁺`

Write `c = ⟨α, ĥ⟩` (`c² = 2m`), `y₀ = P(e^α) = ½E` and

`T = (ω − m/4) ∗ ((ω − 1/16) ∗ ((ω − 9/16) ∗ y₀))`.

`eRel_mem_O : (c³ − 2c) • T ∈ O(V⁺)` — a kernel-checked certificate (`eCert_check`): an explicit
combination, with coefficients polynomial in `c`, of Frenkel–Zhu residues `Pres(a, P(b ⊗ e^α), n)`
(`a` a word state of `M(1)⁺`) and of `(L(−1) + L(0))P(b ⊗ e^α)`, found by exact linear algebra
over `ℚ[c]` (`scratchpad/q3b/certE.py`).  The certificate is uniform in `m`: the variable `c` is
symbolic (`PlusUnitaryCharged.lean`).

Consequently, on a lowest-weight vector `x` of weight `h`,
`(c³ − 2c)·(h − m/4)(h − 1/16)(h − 9/16)·o(E)x = 0`, and `c³ − 2c = c(2m − 2) ≠ 0` for `m ≥ 2`:

`plusERelation_holds : 2 ≤ m → PlusERelation m hm` (**H2 is a theorem**).

This is the relation behind Dong–Nagatomo's classification of irreducible `V_L⁺`-modules
(Comm. Math. Phys. 202 (1999), §5): `o(E)` can be nonzero on a top level only at
`h ∈ {m/4, 1/16, 9/16}`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## §1  Inhomogeneous charged products -/

/-- `Y(Q, z)_s P` for a charged raw polynomial whose words may have different weights. -/
def polyActWC (Q : RawPoly ℕ) (s : ℤ) (P : RawPoly ℕ) : RawPoly ℕ :=
  P.flatMap fun t => polyActC Q s (wWtC t.2) [t]

theorem evRc_singleton (c : ℂ) (t : ℚ × List ℕ) :
    evRc (a0 m) c [t] = ((t.1 : ℚ) : ℂ) • evalWord (xvc (a0 m) c) t.2 := by
  rw [evRc_cons, evRc_nil, add_zero]

theorem V2m_smul_evRcW (Q : RawPoly ℕ) (n : ℤ) (δ : (latP m).carrier) :
    ∀ P : RawPoly ℕ, (V2m m hm).smul (latStateGen (latP m) (evR (a0 m) Q) 0) n
        (latStateGen (latP m) (evRc (a0 m) (chargeCoord (latP m) δ (a0 m)) P) δ) =
      latStateGen (latP m) (evRc (a0 m) (chargeCoord (latP m) δ (a0 m)) (polyActWC Q (-n - 1) P)) δ
  | [] => by
    rw [polyActWC, List.flatMap_nil, evRc_nil]
    simp [latStateGen]
  | t :: P => by
    have hsplit : ∀ c : ℂ, evRc (a0 m) c (t :: P) = evRc (a0 m) c [t] + evRc (a0 m) c P := by
      intro c; rw [evRc_cons, evRc_singleton]
    rw [hsplit, latStateGen_add_boson, PreVertexAlgebra.smul_add_right,
      V2m_smul_evRc m hm Q [t] n (wWtC t.2) δ (by simp), V2m_smul_evRcW Q n δ P,
      show polyActWC Q (-n - 1) (t :: P) = polyActC Q (-n - 1) (wWtC t.2) [t] ++ polyActWC Q (-n - 1) P
        from rfl, evRc_append, latStateGen_add_boson]

/-! ## §2  Charged states of `V⁺` with polynomial descriptions -/

/-- The charge `α`. -/
noncomputable abbrev al : (latP m).carrier := ((1 : ℤ) : (latP m).carrier)

/-- `P(p ⊗ e^α)` for the charged polynomial `p` (variable `0` = `c`). -/
noncomputable def stP (P : RawPoly ℕ) : VP m hm :=
  PP m hm (latStateGen (latP m) (evRc (a0 m) (cα m) P) (al m))

/-- `y` is described by the charged polynomial `P`. -/
def HasC (y : VP m hm) (P : RawPoly ℕ) : Prop := y = stP m hm P

theorem hasC_stP (P : RawPoly ℕ) : HasC m hm (stP m hm P) P := rfl

theorem hasC_add {y z : VP m hm} {P Q : RawPoly ℕ} (hy : HasC m hm y P) (hz : HasC m hm z Q) :
    HasC m hm (y + z) (P ++ Q) := by
  rw [HasC, hy, hz, stP, stP, stP, evRc_append, latStateGen_add_boson, map_add]

theorem hasC_smul {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) (q : ℚ) :
    HasC m hm (((q : ℚ) : ℂ) • y) (scaleR q P) := by
  rw [HasC, hy, stP, stP, evRc_scaleR, latStateGen_csmul, map_smul]

theorem hasC_zero : HasC m hm 0 ([] : RawPoly ℕ) := by
  rw [HasC, stP, evRc_nil]; simp [latStateGen]

theorem hasC_normR {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) : HasC m hm y (normR P) := by
  rw [HasC, hy, stP, stP, evRc_normR]

theorem hasC_of_normR_eq {y : VP m hm} {P P' : RawPoly ℕ} (hy : HasC m hm y P)
    (h : normR P = normR P') : HasC m hm y P' := by
  rw [HasC, hy, stP, stP, ← evRc_normR (a0 m) (cα m) P, h, evRc_normR]

theorem hasC_c {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) :
    HasC m hm (cα m • y) (prependC 0 P) := by
  rw [HasC, hy, stP, stP, evRc_prependC, show xvc (a0 m) (cα m) 0 = MvPolynomial.C (cα m) from rfl,
    ← MvPolynomial.smul_eq_C_mul, latStateGen_csmul, map_smul]

theorem hasC_sum_range (n : ℕ) (f : ℕ → VP m hm) (F : ℕ → RawPoly ℕ)
    (hf : ∀ i, HasC m hm (f i) (F i)) :
    HasC m hm (∑ i ∈ Finset.range n, f i) ((List.range n).flatMap F) := by
  induction n with
  | zero => simpa using hasC_zero m hm
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact hasC_add m hm ih (hf n)

/-- Products with a neutral polynomial state. -/
theorem hasC_smul_left {w : VP m hm} {Q : RawPoly ℕ}
    (hw : (w : LatModuleGen (latP m)) = latStateGen (latP m) (evR (a0 m) Q) 0)
    {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) (n : ℤ) :
    HasC m hm ((V2mPlus m hm).smul w n y) (polyActWC Q (-n - 1) P) := by
  rw [HasC, hy, stP, stP]
  have h := smul_fixed_PP m hm (w : LatModuleGen (latP m)) w.2 n
    (latStateGen (latP m) (evRc (a0 m) (cα m) P) (al m))
  simp only [Subtype.coe_eta] at h
  rw [h, hw]
  exact congrArg (PP m hm) (V2m_smul_evRcW m hm Q n (al m) P)

theorem incl_mkW_coe (b : List ℕ) (hb : Even b.length) :
    ((incl m hm (mkW m hm b hb) : VP m hm) : LatModuleGen (latP m)) =
      latStateGen (latP m) (evR (a0 m) [(1, b)]) 0 := hasPoly_mkW m hm b hb

theorem omega_coe : (((V2mPlus m hm).conformalVector : VP m hm) : LatModuleGen (latP m)) =
    latStateGen (latP m) (evR (a0 m) omR) 0 := hasPoly_omega m hm

/-! ## §3  The Zhu product and the Frenkel–Zhu residues -/

/-- The polynomial of `s ∗ y`, `s` of weight `k`. -/
def zhuRC (k : ℕ) (Q P : RawPoly ℕ) : RawPoly ℕ :=
  (List.range (k + 1)).flatMap fun i => scaleR (k.choose i : ℚ) (polyActWC Q (-(i : ℤ)) P)

/-- The polynomial of `Pres s y n`, `s` of weight `k`. -/
def presRC (k : ℕ) (Q P : RawPoly ℕ) (n : ℕ) : RawPoly ℕ :=
  (List.range (k + n + 1)).flatMap fun i =>
    scaleR ((k + n).choose i : ℚ) (polyActWC Q ((n : ℤ) + 1 - i) P)

theorem hasC_zhuMul {s : VP m hm} {k : ℕ} (hs : s ∈ (V2mPlus m hm).grading (k : ℤ)) {Q : RawPoly ℕ}
    (hQ : (s : LatModuleGen (latP m)) = latStateGen (latP m) (evR (a0 m) Q) 0)
    {y : VP m hm} {P : RawPoly ℕ} (hP : HasC m hm y P) :
    HasC m hm (zhuMul (V2mPlus m hm) s y) (zhuRC k Q P) := by
  rw [zhuMul_homogeneous _ hs, show ((k : ℤ)).toNat = k by simp, zhuRC]
  refine hasC_sum_range m hm _ _ _ fun i => ?_
  by_cases hi : i ≤ k
  · rw [cbz_natCast_eq_choose hi, show ((k.choose i : ℕ) : ℂ) = (((k.choose i : ℚ)) : ℂ) by push_cast; rfl]
    have := hasC_smul_left m hm hQ hP ((i : ℤ) - 1)
    rw [show -((i : ℤ) - 1) - 1 = -(i : ℤ) by ring] at this
    exact hasC_smul m hm this _
  · rw [cbz_nat_eq_zero (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    have := hasC_smul m hm (hasC_smul_left m hm hQ hP ((i : ℤ) - 1)) 0
    rwa [show -((i : ℤ) - 1) - 1 = -(i : ℤ) by ring, Rat.cast_zero] at this

theorem hasC_Pres {s : VP m hm} (k : ℕ) {Q : RawPoly ℕ}
    (hQ : (s : LatModuleGen (latP m)) = latStateGen (latP m) (evR (a0 m) Q) 0)
    {y : VP m hm} {P : RawPoly ℕ} (hP : HasC m hm y P) (n : ℕ) :
    HasC m hm (Pres (V2mPlus m hm) k s y n) (presRC k Q P n) := by
  rw [Pres, presRC]
  refine hasC_sum_range m hm _ _ _ fun i => ?_
  by_cases hi : i ≤ k + n
  · rw [show ((k : ℤ) + n) = (((k + n : ℕ)) : ℤ) by push_cast; ring, cbz_natCast_eq_choose hi,
      show (((k + n).choose i : ℕ) : ℂ) = ((((k + n).choose i : ℚ)) : ℂ) by push_cast; rfl]
    have := hasC_smul_left m hm hQ hP ((i : ℤ) - 2 - n)
    rw [show -((i : ℤ) - 2 - n) - 1 = (n : ℤ) + 1 - i by ring] at this
    exact hasC_smul m hm this _
  · rw [show ((k : ℤ) + n) = (((k + n : ℕ)) : ℤ) by push_cast; ring, cbz_nat_eq_zero (by omega),
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    have := hasC_smul m hm (hasC_smul_left m hm hQ hP ((i : ℤ) - 2 - n)) 0
    rwa [show -((i : ℤ) - 2 - n) - 1 = (n : ℤ) + 1 - i by ring, Rat.cast_zero] at this

/-- The polynomial of `(L(−1) + L(0))y`. -/
def tRC (P : RawPoly ℕ) : RawPoly ℕ := polyActWC omR (-1) P ++ polyActWC omR (-2) P

theorem hasC_T {y : VP m hm} {P : RawPoly ℕ} (hP : HasC m hm y P) :
    HasC m hm ((V2mPlus m hm).L (-1) y + (V2mPlus m hm).L 0 y) (tRC P) := by
  have h1 := hasC_smul_left m hm (omega_coe m hm) hP 0
  have h2 := hasC_smul_left m hm (omega_coe m hm) hP 1
  exact hasC_add m hm h1 h2

theorem T_mem_O (y : VP m hm) : (V2mPlus m hm).L (-1) y + (V2mPlus m hm).L 0 y ∈ O (V2mPlus m hm) := by
  have := gen_mem_O (V2mPlus m hm) y (V2mPlus m hm).vacuum
  rwa [zhuMul_vacuum_right] at this

/-! ## §4  Certificates -/

/-- `c^e·P`. -/
def cpow (e : ℕ) (P : RawPoly ℕ) : RawPoly ℕ := P.map fun t => (t.1, List.replicate e 0 ++ t.2)

theorem cpow_succ (e : ℕ) (P : RawPoly ℕ) : cpow (e + 1) P = prependC 0 (cpow e P) := by
  simp [cpow, prependC, List.replicate_succ]

theorem hasC_cpow {y : VP m hm} {P : RawPoly ℕ} (hy : HasC m hm y P) (e : ℕ) :
    HasC m hm (cα m ^ e • y) (cpow e P) := by
  induction e with
  | zero => simpa [cpow] using hy
  | succ e ih => rw [cpow_succ, pow_succ, mul_comm, mul_smul]; exact hasC_c m hm ih

/-- A certificate entry: a polynomial in `c` (as `(q, e)` pairs), a neutral word `a`, a charged
word `b`, and `n`.  If `a = []` the generator is `(L(−1) + L(0))P(b ⊗ e^α)`, otherwise
`Pres(a, P(b ⊗ e^α), n)`. -/
abbrev CEntry := List (ℚ × ℕ) × List ℕ × List ℕ × ℕ

/-- The generator polynomial of an entry. -/
def genC (t : CEntry) : RawPoly ℕ :=
  normR (if t.2.1 = [] then tRC [(1, t.2.2.1)] else presRC (wWt t.2.1) [(1, t.2.1)] [(1, t.2.2.1)] t.2.2.2)

/-- Multiply by a polynomial in `c`. -/
def cmulR (cs : List (ℚ × ℕ)) (G : RawPoly ℕ) : RawPoly ℕ :=
  cs.flatMap fun qe => scaleR qe.1 (cpow qe.2 G)

/-- The polynomial of a certificate. -/
def certC (L : List CEntry) : RawPoly ℕ := L.flatMap fun t => cmulR t.1 (genC t)

theorem hasC_cmulR {y : VP m hm} {G : RawPoly ℕ} (hy : HasC m hm y G) :
    ∀ cs : List (ℚ × ℕ), ∃ z ∈ Submodule.span ℂ {y}, HasC m hm z (cmulR cs G)
  | [] => ⟨0, Submodule.zero_mem _, hasC_zero m hm⟩
  | qe :: cs => by
    obtain ⟨z, hz, hzC⟩ := hasC_cmulR hy cs
    refine ⟨((qe.1 : ℚ) : ℂ) • (cα m ^ qe.2 • y) + z, Submodule.add_mem _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))) hz, ?_⟩
    exact hasC_add m hm (hasC_smul m hm (hasC_cpow m hm hy qe.2) qe.1) hzC

theorem genC_mem (t : CEntry) (ht : Even t.2.1.length) :
    ∃ y ∈ O (V2mPlus m hm), HasC m hm y (genC t) := by
  unfold genC
  suffices H : ∃ y ∈ O (V2mPlus m hm), HasC m hm y
      (if t.2.1 = [] then tRC [(1, t.2.2.1)] else presRC (wWt t.2.1) [(1, t.2.1)] [(1, t.2.2.1)] t.2.2.2) by
    obtain ⟨y, hy, hyC⟩ := H
    exact ⟨y, hy, hasC_normR m hm hyC⟩
  split_ifs with h
  · exact ⟨_, T_mem_O m hm _, hasC_T m hm (hasC_stP m hm _)⟩
  · refine ⟨_, Pres_mem_O _ ((incl_gradedHom m hm).map_grading (mkW_mem_grading m hm _ ht)) _ _,
      hasC_Pres m hm _ (incl_mkW_coe m hm _ ht) (hasC_stP m hm _) _⟩

theorem certC_mem (L : List CEntry) (hL : ∀ t ∈ L, Even t.2.1.length) :
    ∃ y ∈ O (V2mPlus m hm), HasC m hm y (certC L) := by
  induction L with
  | nil => exact ⟨0, Submodule.zero_mem _, hasC_zero m hm⟩
  | cons t L ih =>
    obtain ⟨y, hy, hyC⟩ := ih fun t ht => hL t (List.mem_cons_of_mem _ ht)
    obtain ⟨g, hg, hgC⟩ := genC_mem m hm t (hL t List.mem_cons_self)
    obtain ⟨z, hz, hzC⟩ := hasC_cmulR m hm hgC t.1
    have hzO : z ∈ O (V2mPlus m hm) :=
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hg)) hz
    exact ⟨z + y, Submodule.add_mem _ hzO hy, hasC_add m hm hzC hyC⟩

/-! ## §5  The target -/

/-- `y₀ = P(e^α)`, `y₁ = (ω − 9/16) ∗ y₀`, `y₂ = (ω − 1/16) ∗ y₁`, `y₃ = (ω − m/4) ∗ y₂`. -/
noncomputable def y0 : VP m hm := stP m hm [(1, [])]
noncomputable def y1 : VP m hm := zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector (y0 m hm) - (9 / 16 : ℂ) • y0 m hm
noncomputable def y2 : VP m hm := zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector (y1 m hm) - (1 / 16 : ℂ) • y1 m hm
noncomputable def y3 : VP m hm := zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector (y2 m hm) - ((m : ℂ) / 4) • y2 m hm

def Y0 : RawPoly ℕ := [(1, [])]
def Y1 : RawPoly ℕ := normR (zhuRC 2 omR Y0 ++ scaleR (-9 / 16) Y0)
def Y2 : RawPoly ℕ := normR (zhuRC 2 omR Y1 ++ scaleR (-1 / 16) Y1)
def Y3 : RawPoly ℕ := normR (zhuRC 2 omR Y2 ++ scaleR (-1 / 8) (prependC 0 (prependC 0 Y2)))
/-- `(c³ − 2c)·y₃`. -/
def Ytgt : RawPoly ℕ := normR (prependC 0 (prependC 0 (prependC 0 Y3)) ++ scaleR (-2) (prependC 0 Y3))

theorem omega_mem : (V2mPlus m hm).conformalVector ∈ (V2mPlus m hm).grading ((2 : ℕ) : ℤ) :=
  (V2mPlus m hm).conformal_mem

theorem hasC_sub_smul {y z : VP m hm} {P Q : RawPoly ℕ} (hy : HasC m hm y P) (hz : HasC m hm z Q)
    (q : ℚ) : HasC m hm (y - ((-q : ℚ) : ℂ) • z) (P ++ scaleR q Q) := by
  have := hasC_add m hm hy (hasC_smul m hm hz q)
  convert this using 1
  push_cast; rw [neg_smul, sub_neg_eq_add]

theorem hasC_y1 : HasC m hm (y1 m hm) Y1 := by
  refine hasC_normR m hm ?_
  have := hasC_sub_smul m hm (hasC_zhuMul m hm (omega_mem m hm) (omega_coe m hm) (hasC_stP m hm Y0))
    (hasC_stP m hm Y0) (-9 / 16)
  convert this using 1
  rw [y1, y0, Y0]; norm_num

theorem hasC_y2 : HasC m hm (y2 m hm) Y2 := by
  refine hasC_normR m hm ?_
  have := hasC_sub_smul m hm (hasC_zhuMul m hm (omega_mem m hm) (omega_coe m hm) (hasC_y1 m hm))
    (hasC_y1 m hm) (-1 / 16)
  convert this using 1
  rw [y2]; norm_num

theorem hasC_y3 : HasC m hm (y3 m hm) Y3 := by
  refine hasC_normR m hm ?_
  have h2 := hasC_c m hm (hasC_c m hm (hasC_y2 m hm))
  have := hasC_sub_smul m hm (hasC_zhuMul m hm (omega_mem m hm) (omega_coe m hm) (hasC_y2 m hm))
    h2 (-1 / 8)
  convert this using 1
  rw [y3, smul_smul, smul_smul, mul_assoc, cα_sq m hm]
  congr 2
  push_cast; ring

theorem hasC_tgt : HasC m hm ((cα m ^ 3 - 2 * cα m) • y3 m hm) Ytgt := by
  refine hasC_normR m hm ?_
  have h3 := hasC_c m hm (hasC_c m hm (hasC_c m hm (hasC_y3 m hm)))
  have h1 := hasC_smul m hm (hasC_c m hm (hasC_y3 m hm)) (-2)
  convert hasC_add m hm h3 h1 using 1
  rw [smul_smul, smul_smul, smul_smul, sub_smul]
  push_cast
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2 <;> ring

def eCert0 : List CEntry :=
  [([(((-27 : ℚ) / 512), 1), (((507 : ℚ) / 1024), 3), (((-39 : ℚ) / 64), 5), (((3 : ℚ) / 16), 7)], [], [], 0),
   ([(((20205 : ℚ) / 512), 2), (((-151 : ℚ) / 32), 4), (((17 : ℚ) / 8), 6)], [], [1], 0),
   ([(((-113557 : ℚ) / 256), 0), (((34377 : ℚ) / 128), 2), (((117 : ℚ) / 32), 4), (((5 : ℚ) / 4), 6)], [], [2], 0),
   ([(((-8967 : ℚ) / 64), 1), (((377 : ℚ) / 64), 3), (((59 : ℚ) / 8), 5)], [], [1, 1], 0),
   ([(((-367367 : ℚ) / 128), 0), (((7071 : ℚ) / 8), 2), (((23 : ℚ) / 2), 4)], [], [3], 0),
   ([(((-80981 : ℚ) / 64), 1), (((2635 : ℚ) / 16), 3), (((17 : ℚ) / 2), 5)], [], [2, 1], 0),
   ([(((-20433 : ℚ) / 32), 0), (((-1881 : ℚ) / 32), 2), (((67 : ℚ) / 4), 4)], [], [1, 1, 1], 0),
   ([(((-15099 : ℚ) / 2), 0), (((3171 : ℚ) / 2), 2), (((11 : ℚ) / 2), 4)], [], [4], 0),
   ([(((-19125 : ℚ) / 4), 1), (((1831 : ℚ) / 4), 3)], [], [3, 1], 0),
   ([(((9889 : ℚ) / 8), 1), (((121 : ℚ) / 4), 3), (((11 : ℚ) / 4), 5)], [], [2, 2], 0),
   ([(((-72759 : ℚ) / 32), 0), (((-645 : ℚ) / 8), 2), (((199 : ℚ) / 4), 4)], [], [2, 1, 1], 0),
   ([(((135 : ℚ) / 8), 1), (((227 : ℚ) / 16), 3)], [], [1, 1, 1, 1], 0),
   ([(((-41241 : ℚ) / 4), 0), ((1564 : ℚ), 2)], [], [5], 0),
   ([(((-12823 : ℚ) / 2), 1), ((533 : ℚ), 3)], [], [4, 1], 0),
   ([(((3877 : ℚ) / 2), 1), ((74 : ℚ), 3)], [], [3, 2], 0)]

def eCert1 : List CEntry :=
  [([(((-55027 : ℚ) / 16), 0), (((-233 : ℚ) / 2), 2), ((60 : ℚ), 4)], [], [3, 1, 1], 0),
   ([(((4305 : ℚ) / 16), 0), (((423 : ℚ) / 2), 2), (((13 : ℚ) / 2), 4)], [], [2, 2, 1], 0),
   ([(((843 : ℚ) / 4), 1), (((73 : ℚ) / 2), 3)], [], [2, 1, 1, 1], 0),
   ([((146 : ℚ), 0), (((37 : ℚ) / 8), 2)], [], [1, 1, 1, 1, 1], 0),
   ([(((-115745 : ℚ) / 16), 0), ((792 : ℚ), 2)], [], [6], 0),
   ([((-3912 : ℚ), 1), ((300 : ℚ), 3)], [], [5, 1], 0),
   ([((1019 : ℚ), 1), ((52 : ℚ), 3)], [], [4, 2], 0),
   ([(((-9369 : ℚ) / 4), 0), ((-13 : ℚ), 2), ((40 : ℚ), 4)], [], [4, 1, 1], 0),
   ([((228 : ℚ), 1)], [], [3, 3], 0),
   ([(((-5779 : ℚ) / 16), 0), ((257 : ℚ), 2)], [], [3, 2, 1], 0),
   ([(((513 : ℚ) / 2), 1), ((31 : ℚ), 3)], [], [3, 1, 1, 1], 0),
   ([(((4965 : ℚ) / 8), 0), ((-29 : ℚ), 2), ((2 : ℚ), 4)], [], [2, 2, 2], 0),
   ([((114 : ℚ), 1), ((2 : ℚ), 3)], [], [2, 2, 1, 1], 0),
   ([(((1031 : ℚ) / 4), 0), (((35 : ℚ) / 2), 2)], [], [2, 1, 1, 1, 1], 0),
   ([((-6 : ℚ), 1)], [], [1, 1, 1, 1, 1, 1], 0)]

def eCert2 : List CEntry :=
  [([(((-16375 : ℚ) / 8), 0), ((160 : ℚ), 2)], [], [7], 0),
   ([((-916 : ℚ), 1), ((68 : ℚ), 3)], [], [6, 1], 0),
   ([((251 : ℚ), 1), ((10 : ℚ), 3)], [], [5, 2], 0),
   ([(((-2689 : ℚ) / 4), 0), ((23 : ℚ), 2), ((10 : ℚ), 4)], [], [5, 1, 1], 0),
   ([((52 : ℚ), 1)], [], [4, 3], 0),
   ([(((-189 : ℚ) / 8), 0), ((74 : ℚ), 2)], [], [4, 2, 1], 0),
   ([((69 : ℚ), 1), ((10 : ℚ), 3)], [], [4, 1, 1, 1], 0),
   ([((-121 : ℚ), 0), ((18 : ℚ), 2)], [], [3, 3, 1], 0),
   ([(((4309 : ℚ) / 16), 0), ((-20 : ℚ), 2)], [], [3, 2, 2], 0),
   ([((135 : ℚ), 1), ((4 : ℚ), 3)], [], [3, 2, 1, 1], 0),
   ([(((173 : ℚ) / 2), 0), ((-1 : ℚ), 2)], [], [3, 1, 1, 1, 1], 0),
   ([((-26 : ℚ), 1), ((-4 : ℚ), 3)], [], [2, 2, 2, 1], 0),
   ([((25 : ℚ), 0), ((14 : ℚ), 2)], [], [2, 2, 1, 1, 1], 0),
   ([((-6 : ℚ), 1)], [], [2, 1, 1, 1, 1, 1], 0),
   ([(((51939 : ℚ) / 512), 1)], [0, 0], [], 0)]

def eCert3 : List CEntry :=
  [([(((-38085 : ℚ) / 128), 1)], [0, 0], [], 1),
   ([(((13557 : ℚ) / 256), 0)], [0, 0], [1], 0),
   ([(((105435 : ℚ) / 128), 1)], [0, 0], [], 2),
   ([(((61629 : ℚ) / 128), 0)], [0, 0], [1], 1),
   ([(((55 : ℚ) / 64), 1)], [0, 0], [1, 1], 0),
   ([(((57185 : ℚ) / 256), 0)], [0, 0], [2], 0),
   ([(((-26127 : ℚ) / 512), 1)], [1, 1], [], 0),
   ([(((-93807 : ℚ) / 64), 1)], [0, 0], [], 3),
   ([(((-42581 : ℚ) / 32), 0)], [0, 0], [1], 2),
   ([(((2847 : ℚ) / 16), 1)], [0, 0], [1, 1], 1),
   ([(((3077 : ℚ) / 32), 0)], [0, 0], [1, 1, 1], 0),
   ([(((2135 : ℚ) / 2), 0)], [0, 0], [2], 1),
   ([(((-3715 : ℚ) / 64), 1)], [0, 0], [2, 1], 0),
   ([(((204427 : ℚ) / 128), 0)], [0, 0], [3], 0),
   ([(((467 : ℚ) / 16), 1)], [1, 1], [], 1)]

def eCert4 : List CEntry :=
  [([(((-57231 : ℚ) / 256), 0)], [1, 1], [1], 0),
   ([(((41091 : ℚ) / 32), 1)], [0, 0], [], 4),
   ([(((3101 : ℚ) / 4), 0)], [0, 0], [1], 3),
   ([(((-2837 : ℚ) / 16), 1)], [0, 0], [1, 1], 2),
   ([(((-2151 : ℚ) / 16), 0)], [0, 0], [1, 1, 1], 1),
   ([(((3 : ℚ) / 4), 1)], [0, 0], [1, 1, 1, 1], 0),
   ([(((-11303 : ℚ) / 16), 0)], [0, 0], [2], 2),
   ([(((3157 : ℚ) / 32), 1)], [0, 0], [2, 1], 1),
   ([(((999 : ℚ) / 16), 0)], [0, 0], [2, 1, 1], 0),
   ([(((651 : ℚ) / 64), 1)], [0, 0], [2, 2], 0),
   ([(((2005 : ℚ) / 4), 0)], [0, 0], [3], 1),
   ([(((68913 : ℚ) / 32), 0)], [0, 0], [4], 0),
   ([(((-15 : ℚ) / 16), 1)], [1, 1], [], 2),
   ([(((1447 : ℚ) / 8), 0)], [1, 1], [1], 1),
   ([(((735 : ℚ) / 4), 0)], [1, 1], [2], 0)]

def eCert5 : List CEntry :=
  [([(((-933 : ℚ) / 2), 1), ((-9 : ℚ), 3)], [0, 0], [], 5),
   ([(((4831 : ℚ) / 16), 0), ((31 : ℚ), 2), ((-7 : ℚ), 4)], [0, 0], [1], 4),
   ([(((1725 : ℚ) / 8), 1), (((3 : ℚ) / 4), 3), (((-5 : ℚ) / 2), 5)], [0, 0], [1, 1], 3),
   ([(((-519 : ℚ) / 4), 0), (((-43 : ℚ) / 4), 2), (((-5 : ℚ) / 2), 4)], [0, 0], [1, 1, 1], 2),
   ([(((-149 : ℚ) / 4), 1), (((-5 : ℚ) / 2), 3)], [0, 0], [1, 1, 1, 1], 1),
   ([((3 : ℚ), 2)], [0, 0], [1, 1, 1, 1, 1], 0),
   ([(((-1683 : ℚ) / 8), 0), (((-237 : ℚ) / 4), 2), (((-5 : ℚ) / 2), 4)], [0, 0], [2], 3),
   ([(((-945 : ℚ) / 4), 1), (((-27 : ℚ) / 2), 3)], [0, 0], [2, 1], 2),
   ([(((-1227 : ℚ) / 16), 0), ((-64 : ℚ), 2), ((4 : ℚ), 4)], [0, 0], [2, 1, 1], 1),
   ([(((169 : ℚ) / 8), 1), (((-23 : ℚ) / 4), 3)], [0, 0], [2, 1, 1, 1], 0),
   ([((26 : ℚ), 1), ((4 : ℚ), 3)], [0, 0], [2, 2], 1),
   ([(((27 : ℚ) / 32), 0), ((24 : ℚ), 2)], [0, 0], [2, 2, 1], 0),
   ([(((-6695 : ℚ) / 16), 0), ((-8 : ℚ), 2)], [0, 0], [3], 2),
   ([(((-407 : ℚ) / 4), 1), (((5 : ℚ) / 2), 3)], [0, 0], [3, 1], 1),
   ([(((1487 : ℚ) / 16), 0), (((-319 : ℚ) / 8), 2), (((9 : ℚ) / 4), 4)], [0, 0], [3, 1, 1], 0)]

def eCert6 : List CEntry :=
  [([(((549 : ℚ) / 8), 1), (((9 : ℚ) / 4), 3)], [0, 0], [3, 2], 0),
   ([(((621 : ℚ) / 4), 0), (((9 : ℚ) / 2), 2)], [0, 0], [4], 1),
   ([(((14919 : ℚ) / 16), 0)], [0, 0], [5], 0),
   ([(((-309 : ℚ) / 8), 0)], [1, 1], [1], 2),
   ([(((-347 : ℚ) / 4), 1), ((12 : ℚ), 3), (((-1 : ℚ) / 2), 5)], [1, 1], [1, 1], 1),
   ([(((-219 : ℚ) / 4), 0)], [1, 1], [1, 1, 1], 0),
   ([(((-347 : ℚ) / 4), 0), (((-1 : ℚ) / 2), 4)], [1, 1], [2], 1),
   ([(((219 : ℚ) / 2), 0)], [1, 1], [3], 0),
   ([(((525 : ℚ) / 4), 0)], [2, 2], [1], 0)]

def eCert : List CEntry := eCert0 ++ eCert1 ++ eCert2 ++ eCert3 ++ eCert4 ++ eCert5 ++ eCert6

theorem eCert_even : ∀ t ∈ eCert, _root_.Even t.2.1.length := by decide

theorem eCert_check : normR (certC eCert) = normR Ytgt := by
  decide +kernel

/-- **The `E`-relation**: `(c³ − 2c)·(ω − m/4) ∗ (ω − 1/16) ∗ (ω − 9/16) ∗ P(e^α) ∈ O(V⁺)`. -/
theorem eRel_mem_O : (cα m ^ 3 - 2 * cα m) • y3 m hm ∈ O (V2mPlus m hm) := by
  obtain ⟨y, hy, hyC⟩ := certC_mem m hm eCert eCert_even
  have h := hasC_of_normR_eq m hm hyC eCert_check
  rw [HasC] at h
  rw [hasC_tgt m hm, ← h]
  exact hy

/-! ## §6  H2 on top vectors -/

include hm in
theorem cα_poly_ne_zero (hm2 : 2 ≤ m) : cα m ^ 3 - 2 * cα m ≠ 0 := by
  have h : cα m ^ 3 - 2 * cα m = cα m * (cα m * cα m - 2) := by ring
  rw [h, cα_sq m hm]
  refine mul_ne_zero (cα_ne_zero m hm) ?_
  intro h2
  have h3 : (m : ℂ) = 1 := by linear_combination h2 / 2
  have h4 : m = 1 := by exact_mod_cast h3
  omega

theorem EP_eq_y0 : EP m hm = (2 : ℂ) • y0 m hm := by
  have h1 : evRc (a0 m) (cα m) [(1, [])] = 1 := by
    rw [evRc_cons, evRc_nil, add_zero, evalWordC_nil]; simp
  rw [y0, stP, h1]
  change xP m hm ((1 : ℤ) : (latP m).carrier) = _
  rw [show (1 : FockN (rank (latP m))) = 1 from rfl, PP_eAlpha, smul_smul]
  norm_num

theorem oMod_omega_zhuMul {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M)
    {h : ℂ} (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) (v : VP m hm) :
    oMod N (zhuMul (V2mPlus m hm) (V2mPlus m hm).conformalVector v) x = h • oMod N v x := by
  rw [oMod_zhuMul_lowest_all N hcw _ _ hx, oMod_homogeneous N (V2mPlus m hm).conformal_mem,
    show (2 : ℤ) - 1 = 1 by norm_num]
  exact N.L0_weight h _ (oMod_preserves_lowest_all N v hx)

theorem oMod_y3 {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M)
    {h : ℂ} (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) :
    oMod N (y3 m hm) x = ((h - (m : ℂ) / 4) * (h - 1 / 16) * (h - 9 / 16)) • oMod N (y0 m hm) x := by
  simp only [y3, y2, y1, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    oMod_omega_zhuMul m hm N hcw hx]
  module

/-- **H2 is a theorem** (`m ≥ 2`). -/
theorem plusERelation_holds (hm2 : 2 ≤ m) : PlusERelation m hm := by
  intro M _ _ N h x hcw hx
  have h0 := oMod_eq_zero_of_mem_O N hcw (eRel_mem_O m hm) hx
  rw [map_smul, LinearMap.smul_apply, oMod_y3 m hm N hcw hx] at h0
  have h1 := (smul_eq_zero.mp h0).resolve_left (cα_poly_ne_zero m hm hm2)
  rw [EP_eq_y0, map_smul, LinearMap.smul_apply, smul_comm, h1, smul_zero]

end VOA.Classification.COne.PlusUnitary
