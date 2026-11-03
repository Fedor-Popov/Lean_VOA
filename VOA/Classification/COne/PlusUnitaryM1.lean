/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.PlusUnitaryCert
import VOA.Classification.COne.PlusUnitaryReduce

/-!
# The `M(1)⁺` dichotomy on top vectors of `V_{2m}⁺`-modules

On a lowest-weight vector `x` of an ordinary `V_{2m}⁺`-module with `o(ω)x = hx`, `o(W⁴)x = wx`,
the two elements

* `R₁ = W − 2ω − (37/3) ω∗W + 34 ω∗ω + 44 ω∗ω∗W − 88 ω∗ω∗ω − (7/3) W∗W` (weight 8), and
* `R₂ = W∗W − 4ω∗ω + 92 ω³ − (298/9) ω²W − (58/9) ωW² − (656/3) ω⁴ + (328/3) ω³W` (weight 10)

of `M(1)⁺` lie in `O(V⁺)` (kernel-checked certificates `r1_cert`, `r2_cert`: explicit
combinations of Frenkel–Zhu residues `Pres(x₀x₀, ·)`, `Pres(x₀x₂, ·)`, found by exact rational
linear algebra, `scratchpad/q3/cert_m1.py`).  Hence `R₁(h,w) = R₂(h,w) = 0`, and since
`R₁ = (w − 2h)·Q₁`, `R₂ = (w − 2h)·Q₂` with the eliminant of `Q₁, Q₂` equal to
`−(h−1)(16h−9)(16h−1)/21`:

`plusM1Dichotomy_holds : PlusM1Dichotomy m hm` — `w = 2h` or `h ∈ {1/16, 9/16, 1}`.

This is the top-level shadow of the Dong–Nagatomo classification of irreducible `M(1)⁺`-modules
(J. Algebra 216 (1999)): `M(1,λ)` on the curve `w = λ² = 2h`, and `M(1)(θ)^±`, `M(1)⁻` at the
three exceptional points `(1/16, 3/64)`, `(9/16, 147/64)`, `(1, 12)`.  It holds for every `m ≥ 1`.
-/

set_option linter.style.longLine false

namespace VOA.Classification.COne.PlusUnitary

open VOA VOA.LatGen VOA.LatGen.Triplet VOA.IntegralLattice HeisenbergN LatMod MvPolynomial
  VOA.SparseRational PlusC2Eval PlusC2

variable (m : ℕ) (hm : 1 ≤ m)

/-! ## Polynomials in `ω, W` -/

/-- A polynomial `Σ c·x^i w^j` as a list of `(c, i, j)`. -/
abbrev MonoList := List (ℚ × ℕ × ℕ)

/-- Its value at `(h, w)`. -/
def evalML (L : MonoList) (h w : ℂ) : ℂ := (L.map fun t => ((t.1 : ℚ) : ℂ) * (h ^ t.2.1 * w ^ t.2.2)).sum

/-- The corresponding element `Σ c · W^{∗j} ∗ ω^{∗i}` of `M(1)⁺`. -/
noncomputable def lcE (L : MonoList) : (m1Sub m hm).carrier :=
  (L.map fun t => ((t.1 : ℚ) : ℂ) • monoE m hm t.2.1 t.2.2).sum

/-- Its polynomial. -/
def lcR (L : MonoList) : List (ℚ × RawPoly ℕ) := L.map fun t => (t.1, monoR t.2.1 t.2.2)

theorem hasPoly_lcE : ∀ L : MonoList, HasPoly m hm (lcE m hm L) (lc (lcR L))
  | [] => by simpa [lcE, lcR, lc] using hasPoly_zero m hm
  | t :: L => by
    have := hasPoly_add m hm (hasPoly_smul m hm (hasPoly_monoE m hm t.2.1 t.2.2) t.1) (hasPoly_lcE L)
    simpa [lcE, lcR, lc] using this

theorem oMod_lcE {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M)
    {h w : ℂ} (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h)
    (hW : oMod N (WP m hm) x = w • x) :
    ∀ L : MonoList, oMod N (incl m hm (lcE m hm L)) x = evalML L h w • x
  | [] => by simp [lcE, evalML]
  | t :: L => by
    have h1 := oMod_monoE m hm N hcw hx hW t.2.1 t.2.2
    have h2 := oMod_lcE N hcw hx hW L
    simp only [lcE, List.map_cons, List.sum_cons, map_add, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply] at h2 ⊢
    rw [h1, h2, show evalML (t :: L) h w = ((t.1 : ℚ) : ℂ) * (h ^ t.2.1 * w ^ t.2.2) + evalML L h w
      from rfl, add_smul, smul_smul]

/-! ## Certificates land in `O(V⁺)` -/

/-- The submodule of `M(1)⁺` mapped into `O(V⁺)`. -/
noncomputable def OPlus : Submodule ℂ (m1Sub m hm).carrier := (O (V2mPlus m hm)).comap (incl m hm)

theorem ocert_mem_OPlus (L : List OEntry) (hL : ∀ t ∈ L, Even t.2.1.length ∧ Even t.2.2.1.length) :
    ∀ t ∈ ocert L, ∃ x ∈ OPlus m hm, HasPoly m hm x t.2 := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  obtain ⟨ha, hb⟩ := hL e he
  refine ⟨Pres (M1P m hm) (wWt e.2.1) (mkW m hm e.2.1 ha) (mkW m hm e.2.2.1 hb) e.2.2.2, ?_,
    hasPoly_Pres m hm _ (hasPoly_mkW m hm _ ha) (hasPoly_mkW m hm _ hb) _⟩
  change incl m hm _ ∈ O (V2mPlus m hm)
  rw [(incl_gradedHom m hm).map_Pres]
  exact Pres_mem_O _ ((incl_gradedHom m hm).map_grading (mkW_mem_grading m hm _ ha)) _ _

/-- A certified element acts by zero on top vectors. -/
theorem evalML_eq_zero_of_cert {L : MonoList} (C : List OEntry)
    (hC : ∀ t ∈ C, Even t.2.1.length ∧ Even t.2.2.1.length)
    (hcert : normR (lc (lcR L)) = normR (lc (ocert C)))
    {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule (V2mPlus m hm) M)
    {h w : ℂ} (hcw : IsLowestWeight N h) {x : M} (hx : x ∈ N.weight h) (hx0 : x ≠ 0)
    (hW : oMod N (WP m hm) x = w • x) : evalML L h w = 0 := by
  have hmem : lcE m hm L ∈ OPlus m hm :=
    mem_of_cert m hm _ (hasPoly_lcE m hm L) _ (ocert_mem_OPlus m hm C hC) hcert
  have h0 := oMod_eq_zero_of_mem_O N hcw hmem hx
  rw [oMod_lcE m hm N hcw hx hW] at h0
  exact (smul_eq_zero.mp h0).resolve_right hx0

/-! ## The two relations -/

/-- `R₁` (weight 8). -/
def r1T : MonoList := [(-88, 3, 0), (1, 0, 1), (-2, 1, 0), (-37/3, 1, 1), (34, 2, 0), (44, 2, 1), (-7/3, 0, 2)]

/-- `R₂` (weight 10). -/
def r2T : MonoList :=
  [(92, 3, 0), (-298/9, 2, 1), (1, 0, 2), (-4, 2, 0), (-58/9, 1, 2), (-656/3, 4, 0), (328/3, 3, 1)]

/-- The `O`-certificate of `R1`. -/
def r1L : List OEntry :=
  [((-21), [0, 0], [], 0),
   ((1699/2), [0, 0], [], 1),
   ((-3525), [0, 0], [], 2),
   ((2566), [0, 0], [], 3),
   ((-169), [0, 0], [], 4),
   ((-773/4), [0, 0], [0, 0], 0),
   ((-2218), [0, 0], [0, 0], 1),
   ((18615/8), [0, 0], [0, 0], 2),
   ((-745/2), [0, 0], [0, 0], 3),
   ((-986), [0, 0], [0, 1], 0),
   ((-288), [0, 0], [0, 1], 1),
   ((75/2), [0, 0], [0, 1], 2),
   ((-1489), [0, 0], [0, 2], 0),
   ((-109), [0, 0], [0, 2], 1),
   ((-21), [0, 0], [1, 1], 1),
   ((22), [0, 0], [0, 0, 0, 0], 1),
   ((-77/2), [0, 0], [0, 0, 0, 0], 0),
   ((-2705/4), [0, 0], [0, 3], 0),
   ((155/2), [0, 0], [], 5),
   ((-55/2), [0, 0], [0, 0, 0, 1], 0),
   ((10), [0, 2], [], 0),
   ((-555/2), [0, 2], [], 1),
   ((1005/2), [0, 2], [], 2),
   ((425), [0, 2], [], 3),
   ((185/12), [0, 2], [0, 0], 0),
   ((4375/6), [0, 2], [0, 0], 1)]

/-- The `O`-certificate of `R2`. -/
def r2L : List OEntry :=
  [((-30/7), [0, 0], [], 0),
   ((200705/336), [0, 0], [], 1),
   ((459199733/2016), [0, 0], [], 2),
   ((-240432863/336), [0, 0], [], 3),
   ((402851363/504), [0, 0], [], 4),
   ((-2192903/7), [0, 0], [], 5),
   ((-109070149/2016), [0, 0], [], 6),
   ((1324667/24), [0, 0], [], 7),
   ((-396402241/2016), [0, 0], [0, 0], 0),
   ((28723843/112), [0, 0], [0, 0], 1),
   ((-156996647/2016), [0, 0], [0, 0], 2),
   ((-7838623/144), [0, 0], [0, 0], 3),
   ((5807891/504), [0, 0], [0, 0], 4),
   ((-72111413/224), [0, 0], [0, 1], 0),
   ((25014137/72), [0, 0], [0, 1], 1),
   ((-343563245/2016), [0, 0], [0, 1], 2),
   ((-6267845/336), [0, 0], [0, 1], 3),
   ((-51120973/252), [0, 0], [0, 2], 0),
   ((4951447/84), [0, 0], [0, 2], 1),
   ((-14680559/252), [0, 0], [0, 2], 2),
   ((64397/18), [0, 0], [0, 2], 3),
   ((6855595/288), [0, 0], [0, 1], 4),
   ((444197/12), [0, 0], [1, 1], 1),
   ((-449993/18), [0, 0], [1, 1], 2),
   ((-19621/36), [0, 0], [0, 0, 0, 0], 0),
   ((-5534/9), [0, 0], [0, 0, 0, 0], 1),
   ((-118255/36), [0, 0], [0, 0, 0, 0], 2),
   ((10045/3), [0, 0], [0, 0, 0, 0], 3),
   ((-22968755/72), [0, 0], [0, 3], 0),
   ((-47965/3), [0, 0], [0, 3], 1),
   ((-2041225/288), [0, 0], [0, 3], 2),
   ((2972215/144), [0, 0], [0, 0], 5),
   ((-467705/144), [0, 0], [1, 2], 2),
   ((-52895/12), [0, 0], [0, 0, 0, 1], 0),
   ((-25565/9), [0, 0], [0, 0, 0, 1], 1),
   ((18275/36), [0, 0], [0, 0, 0, 1], 2),
   ((-3729769/14), [0, 0], [0, 4], 0),
   ((-92891/9), [0, 0], [0, 4], 1),
   ((-7577891/112), [0, 0], [1, 3], 0),
   ((-444089/36), [0, 0], [1, 3], 1),
   ((444089/72), [0, 0], [1, 1], 3),
   ((-271199/36), [0, 0], [0, 0, 0, 2], 0),
   ((-24695/18), [0, 0], [0, 0, 0, 2], 1),
   ((-29), [0, 0], [0, 0, 1, 1], 1),
   ((82/3), [0, 0], [0, 0, 0, 0, 0, 0], 1),
   ((-287/6), [0, 0], [0, 0, 0, 0, 0, 0], 0),
   ((-2206405/32), [0, 0], [0, 5], 0),
   ((-6802975/288), [0, 0], [1, 4], 0),
   ((-132665/36), [0, 0], [0, 0, 0, 3], 0),
   ((-205/6), [0, 0], [0, 0, 0, 0, 0, 1], 0),
   ((15/7), [0, 2], [], 0),
   ((-199265/1008), [0, 2], [], 1),
   ((-423385/168), [0, 2], [], 2),
   ((11905235/504), [0, 2], [], 3),
   ((-28077545/1008), [0, 2], [], 4),
   ((168055/24), [0, 2], [], 5),
   ((17095/672), [0, 2], [0, 0], 0),
   ((401115/112), [0, 2], [0, 0], 1),
   ((-1143375/224), [0, 2], [0, 0], 2),
   ((125165/24), [0, 2], [0, 0], 3),
   ((-56525/18), [0, 2], [0, 2], 1)]

theorem r1_cert : normR (lc (lcR r1T)) = normR (lc (ocert r1L)) := by
  decide +kernel

theorem r2_cert : normR (lc (lcR r2T)) = normR (lc (ocert r2L)) := by
  decide +kernel

/-- The algebra: `R₁ = R₂ = 0` forces the curve or an exceptional point. -/
theorem dichotomy_of_relations {h w : ℂ} (h1 : evalML r1T h w = 0) (h2 : evalML r2T h w = 0) :
    w = 2 * h ∨ h = 1 / 16 ∨ h = 9 / 16 ∨ h = 1 := by
  simp only [evalML, r1T, r2T, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h1 h2
  push_cast at h1 h2
  by_cases hc : w = 2 * h
  · exact Or.inl hc
  right
  have hc' : w - 2 * h ≠ 0 := sub_ne_zero.mpr hc
  -- `R₁ = (w − 2h) Q₁`, `R₂ = (w − 2h) Q₂`
  have hQ1 : -7 / 3 * w + 44 * h ^ 2 - 17 * h + 1 = 0 := by
    have : (w - 2 * h) * (-7 / 3 * w + 44 * h ^ 2 - 17 * h + 1) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hc'
  have hQ2 : -58 / 9 * w * h + w + 328 / 3 * h ^ 3 - 46 * h ^ 2 + 2 * h = 0 := by
    have : (w - 2 * h) * (-58 / 9 * w * h + w + 328 / 3 * h ^ 3 - 46 * h ^ 2 + 2 * h) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left hc'
  have hP : (h - 1) * (16 * h - 9) * (16 * h - 1) = 0 := by
    linear_combination (-21 : ℂ) * hQ2 + (-9 : ℂ) * (1 - 58 / 9 * h) * hQ1
  rcases mul_eq_zero.mp hP with hP | hP
  · rcases mul_eq_zero.mp hP with hP | hP
    · right; right; linear_combination hP
    · right; left; linear_combination hP / 16
  · left; linear_combination hP / 16

/-- **H1, the `M(1)⁺` dichotomy, is a theorem** (every `m ≥ 1`). -/
theorem plusM1Dichotomy_holds : PlusM1Dichotomy m hm := by
  intro M _ _ N h w x hcw hx hx0 hW
  exact dichotomy_of_relations
    (evalML_eq_zero_of_cert m hm r1L (by decide) r1_cert N hcw hx hx0 hW)
    (evalML_eq_zero_of_cert m hm r2L (by decide) r2_cert N hcw hx hx0 hW)

end VOA.Classification.COne.PlusUnitary
