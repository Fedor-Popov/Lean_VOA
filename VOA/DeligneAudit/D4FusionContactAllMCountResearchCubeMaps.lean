import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubePower
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-! Exact polynomial maps for the three successive cube lowering strings.
Projection to the four nested-chain variables is used only AFTER applying
the whole polynomial operators. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
noncomputable section

variable {K : Type*} [CommRing K] {σ τ : Type*}

/-- The variable check extends to whole polynomials by the Leibniz rule. -/
theorem map_derivation (f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (D : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (E : Derivation K (MvPolynomial τ K) (MvPolynomial τ K))
    (hX : ∀ i, f (D (MvPolynomial.X i)) = E (f (MvPolynomial.X i)))
    (p : MvPolynomial σ K) : f (D p) = E (f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algHom_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
      rw [D.leibniz,map_mul f p (MvPolynomial.X i),E.leibniz]
      simp only [smul_eq_mul,map_add,map_mul,hp,hX]

variable (K : Type*) [CommRing K]
abbrev P4 := MvPolynomial (Fin 4) K
abbrev P8 := MvPolynomial (Fin 8) K

def d1small : Derivation K (P4 K) (P4 K) :=
  MvPolynomial.mkDerivation K ![MvPolynomial.X 1,0,MvPolynomial.X 3,0]

def d2small : Derivation K (P4 K) (P4 K) :=
  MvPolynomial.mkDerivation K ![MvPolynomial.X 2,MvPolynomial.X 3,0,0]

def d1 : Derivation K (P8 K) (P8 K) :=
  MvPolynomial.mkDerivation K ![MvPolynomial.X 1,0,MvPolynomial.X 3,0,
    MvPolynomial.X 5,0,MvPolynomial.X 7,0]

def d2 : Derivation K (P8 K) (P8 K) :=
  MvPolynomial.mkDerivation K ![MvPolynomial.X 2,MvPolynomial.X 3,0,0,
    MvPolynomial.X 6,MvPolynomial.X 7,0,0]

def d3 : Derivation K (P8 K) (P8 K) :=
  MvPolynomial.mkDerivation K ![MvPolynomial.X 4,MvPolynomial.X 5,
    MvPolynomial.X 6,MvPolynomial.X 7,0,0,0,0]

def e2 : Derivation K (P4 K) (P4 K) :=
  MvPolynomial.mkDerivation K ![0,MvPolynomial.X 2,0,0]

def e3 : Derivation K (P4 K) (P4 K) :=
  MvPolynomial.mkDerivation K ![0,0,MvPolynomial.X 3,0]

def smallIndex (i : Fin 4) : Fin 8 := ⟨i.val,by omega⟩

def smallEmbed : P4 K →ₐ[K] P8 K := MvPolynomial.rename smallIndex

/-- Only the four nested-chain colors survive. -/
def chainProj : P8 K →ₐ[K] P4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1,0,MvPolynomial.X 2,
    0,0,0,MvPolynomial.X 3]

def chainProjSmall : P4 K →ₐ[K] P4 K :=
  MvPolynomial.aeval ![MvPolynomial.X 0,MvPolynomial.X 1,0,MvPolynomial.X 2]

theorem embed_d1 (p : P4 K) : smallEmbed K (d1small K p) = d1 K (smallEmbed K p) := by
  apply map_derivation
  intro i
  fin_cases i <;> simp [d1small,d1,smallEmbed,smallIndex]

theorem embed_d2 (p : P4 K) : smallEmbed K (d2small K p) = d2 K (smallEmbed K p) := by
  apply map_derivation
  intro i
  fin_cases i <;> simp [d2small,d2,smallEmbed,smallIndex]

theorem project_d2 (p : P4 K) : chainProjSmall K (d2small K p) = e2 K (chainProjSmall K p) := by
  apply map_derivation
  intro i
  fin_cases i <;> simp [d2small,e2,chainProjSmall]

theorem project_d3 (p : P8 K) : chainProj K (d3 K p) = e3 K (chainProj K p) := by
  apply map_derivation
  intro i
  fin_cases i <;> simp [d3,e3,chainProj]

theorem project_embed : (chainProj K).comp (smallEmbed K) = chainProjSmall K := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [chainProj,smallEmbed,smallIndex,chainProjSmall]

theorem project_embed_apply (p : P4 K) : chainProj K (smallEmbed K p) = chainProjSmall K p :=
  AlgHom.congr_fun (project_embed K) p

end
#print axioms project_d3
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
