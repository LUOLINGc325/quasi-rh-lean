import QRHShort.SecondPoissonAssembly
import QRHShort.PrimaryGenerator
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! Finite harmonic analysis for the literal ray class quotient. All bridges
use the frozen residue characters, primary generators, and Outside condition. -/

noncomputable section
open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.CloudBatch

instance rayClassFinite (c : ArithmeticContext) : Finite (RayClass c) := by
  let : Finite (O ⧸ c.rayModulus) :=
    Ring.HasFiniteQuotients.finiteQuotient c.rayModulus_ne_bot
  infer_instance

instance rayClassFintype (c : ArithmeticContext) : Fintype (RayClass c) :=
  Fintype.ofFinite _

abbrev RayFourierIndex (c : ArithmeticContext) := AddChar (Additive (RayClass c)) ℂ

instance rayFourierIndexFintype (c : ArithmeticContext) : Fintype (RayFourierIndex c) := by
  letI : Fintype (RayClass c) := rayClassFintype c
  exact AddChar.instFintype (Additive (RayClass c)) ℂ

/-- A character of the additive type tag is a multiplicative group character. -/
def characterHom {G : Type*} [CommGroup G] (ψ : AddChar (Additive G) ℂ) : G →* ℂ where
  toFun x := ψ (Additive.ofMul x)
  map_one' := ψ.map_zero_eq_one
  map_mul' x y := ψ.map_add_eq_mul (Additive.ofMul x) (Additive.ofMul y)

/-- Descend a character from residue units modulo global units and extend it
by zero at nonunits, exactly as in the frozen Hecke-character definition. -/
def rayCharacterFromHom (c : ArithmeticContext) (f : RayClass c →* ℂ) :
    RayCharacter c :=
  ⟨{ modulus := c.rayModulus
     modulus_ne_bot := c.rayModulus_ne_bot
     residue := MulChar.ofUnitHom
       (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c)))
     unit_trivial := by
       intro u
       let v : (O ⧸ c.rayModulus)ˣ :=
         Units.map (Ideal.Quotient.mk c.rayModulus).toMonoidHom u
       have hv : (QuotientGroup.mk' (globalUnitImage c)) v = 1 :=
         (QuotientGroup.eq_one_iff v).mpr ⟨u, rfl⟩
       change MulChar.ofUnitHom
         (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c)))
         (v : O ⧸ c.rayModulus) = 1
       rw [MulChar.ofUnitHom_coe]
       simp only [MonoidHom.comp_apply, hv, map_one, Units.val_one] }, rfl⟩

theorem rayCharacterFromHom_onElement (c : ArithmeticContext)
    (f : RayClass c →* ℂ) {x : O}
    (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x)) :
    (rayCharacterFromHom c f).val.onElement x = f (rayClass c x) := by
  unfold HeckeCharacter.onElement rayCharacterFromHom rayClass
  rw [dite_eq_left hx]
  have h := MulChar.ofUnitHom_coe
    (f.toHomUnits.comp (QuotientGroup.mk' (globalUnitImage c))) hx.unit
  simpa only [hx.unit_spec, MonoidHom.comp_apply, MonoidHom.coe_toHomUnits,
    QuotientGroup.mk'_apply] using h

private theorem primaryGenerator_principal_outside (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) : principal (primaryGenerator a) = a := by
  let z := idealGenerator a
  have hz : principal z = a := Ideal.span_singleton_generator a
  have hp : Prime (principal (omega - 1)) :=
    Ideal.prime_span_singleton_iff.mpr omega_sub_one_prime
  have hthree : principal (omega - 1) ∣ principal 3 := by
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr omega_sub_one_dvd_three
  have hnot : ¬ omega - 1 ∣ z := by
    intro hdiv
    apply ha.2 _ (c.above_three _ hp hthree)
    rw [← hz]
    apply Ideal.dvd_span_singleton.mpr
    exact Ideal.mem_span_singleton.mpr hdiv
  obtain ⟨u, hu⟩ := exists_primary_unit_of_not_dvd z hnot
  have hex : ∃ x : O, principal x = a ∧ IsPrimary x :=
    ⟨(u : O) * z, (Ideal.span_singleton_mul_left_unit u.isUnit z).trans hz, hu⟩
  simpa only [primaryGenerator, dite_eq_left hex] using (Classical.choose_spec hex).1

theorem primaryGenerator_unit_rayModulus (c : ArithmeticContext)
    {a : Ideal O} (ha : Outside c.S a) :
    IsUnit (Ideal.Quotient.mk c.rayModulus (primaryGenerator a)) := by
  have hcoprime : IsCoprime a c.rayModulus := by
    apply Ideal.coprime_of_no_prime_ge
    intro p hap hmp hp
    have hp₀ : p ≠ ⊥ := by
      intro h
      exact c.rayModulus_ne_bot (le_bot_iff.mp (h ▸ hmp))
    have hp' := Ideal.prime_of_isPrime hp₀ hp
    exact ha.2 p (c.ray_supported p hp' (Ideal.dvd_iff_le.mpr hmp))
      (Ideal.dvd_iff_le.mpr hap)
  obtain ⟨i, hi, j, hj, hij⟩ := hcoprime.exists
  rw [← primaryGenerator_principal_outside c ha] at hi
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hi
  have h := congrArg (Ideal.Quotient.mk c.rayModulus) hij
  have hj₀ := Ideal.Quotient.eq_zero_iff_mem.mpr hj
  simp only [map_add, map_mul, hj₀, add_zero, map_one] at h
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk c.rayModulus b, h⟩

theorem rayCharacterFromHom_rayValue (c : ArithmeticContext)
    (f : RayClass c →* ℂ) {a : Ideal O} (ha : Outside c.S a) :
    rayValue (rayCharacterFromHom c f).val a = f (idealClass c a) :=
  rayCharacterFromHom_onElement c f (primaryGenerator_unit_rayModulus c ha)

/-- The fixed finite family used for every bounded function at this modulus. -/
def rayFourierCharacter (c : ArithmeticContext) (ψ : RayFourierIndex c) : RayCharacter c :=
  rayCharacterFromHom c (characterHom (G := RayClass c) ψ)

theorem rayFourierCharacter_rayValue (c : ArithmeticContext) (ψ : RayFourierIndex c)
    {a : Ideal O} (ha : Outside c.S a) :
    rayValue (rayFourierCharacter c ψ).val a = ψ (Additive.ofMul (idealClass c a)) :=
  rayCharacterFromHom_rayValue c (characterHom (G := RayClass c) ψ) ha

/-- Transport the residue character along its specified modulus equality. -/
def residueAtRayModulus (c : ArithmeticContext) (ξ : RayCharacter c) :
    MulChar (O ⧸ c.rayModulus) ℂ :=
  ξ.property ▸ ξ.val.residue

theorem residueAtRayModulus_onElement (c : ArithmeticContext) (ξ : RayCharacter c)
    (x : O) :
    residueAtRayModulus c ξ (Ideal.Quotient.mk c.rayModulus x) = ξ.val.onElement x := by
  rcases ξ with ⟨⟨M, hM, r, hu⟩, h⟩
  change M = c.rayModulus at h
  subst M
  rfl

theorem residueAtRayModulus_unit_trivial (c : ArithmeticContext) (ξ : RayCharacter c)
    (u : Oˣ) :
    residueAtRayModulus c ξ (Ideal.Quotient.mk c.rayModulus (u : O)) = 1 := by
  rw [residueAtRayModulus_onElement]
  exact ξ.val.unit_trivial u

def rayUnitHom (c : ArithmeticContext) (ξ : RayCharacter c) :
    (O ⧸ c.rayModulus)ˣ →* ℂ where
  toFun u := residueAtRayModulus c ξ (u : O ⧸ c.rayModulus)
  map_one' := (residueAtRayModulus c ξ).map_one
  map_mul' u v := (residueAtRayModulus c ξ).map_mul u v

theorem globalUnitImage_le_rayUnitHom_ker (c : ArithmeticContext) (ξ : RayCharacter c) :
    globalUnitImage c ≤ (rayUnitHom c ξ).ker := by
  rintro u ⟨v, rfl⟩
  exact residueAtRayModulus_unit_trivial c ξ v

/-- The actual ray character descended to the quotient by global units. -/
def rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c) : RayClass c →* ℂ :=
  QuotientGroup.lift (globalUnitImage c) (rayUnitHom c ξ)
    (globalUnitImage_le_rayUnitHom_ker c ξ)

theorem rayClassCharacter_rayClass (c : ArithmeticContext) (ξ : RayCharacter c)
    {x : O} (hx : IsUnit (Ideal.Quotient.mk c.rayModulus x)) :
    rayClassCharacter c ξ (rayClass c x) = ξ.val.onElement x := by
  unfold rayClass rayClassCharacter
  rw [dite_eq_left hx, QuotientGroup.lift_mk']
  change residueAtRayModulus c ξ (hx.unit : O ⧸ c.rayModulus) = _
  rw [hx.unit_spec, residueAtRayModulus_onElement]

theorem rayValue_eq_rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c)
    {a : Ideal O} (ha : Outside c.S a) :
    rayValue ξ.val a = rayClassCharacter c ξ (idealClass c a) :=
  (rayClassCharacter_rayClass c ξ (primaryGenerator_unit_rayModulus c ha)).symm

/-- Expand any function of the actual ray class as a finitely supported
linear combination of actual ray characters. Equal output characters are
combined by mapDomain, so no injectivity of the indexing map is assumed. -/
theorem class_function_ray_expansion (c : ArithmeticContext) (g : RayClass c → ℂ) :
    ∃ coeffs : RayCharacter c → ℂ, (Function.support coeffs).Finite ∧
      ∀ a : Ideal O, Outside c.S a →
        g (idealClass c a) = ∑' ξ : RayCharacter c, coeffs ξ * rayValue ξ.val a := by
  let : Fintype (RayClass c) := rayClassFintype c
  let l : RayFourierIndex c →₀ ℂ :=
    (AddChar.complexBasis (Additive (RayClass c))).repr (fun x => g x.toMul)
  let m : RayCharacter c →₀ ℂ := l.mapDomain (rayFourierCharacter c)
  refine ⟨(m : RayCharacter c → ℂ), m.hasFiniteSupport, ?_⟩
  intro a ha
  have hb := congr_fun
    ((AddChar.complexBasis (Additive (RayClass c))).linearCombination_repr
      (fun x => g x.toMul)) (Additive.ofMul (idealClass c a))
  have hb' : l.sum (fun ψ v => v * ψ (Additive.ofMul (idealClass c a))) =
      g (idealClass c a) := by
    simpa [l, Finsupp.linearCombination_apply, Finsupp.sum] using hb
  calc
    g (idealClass c a) = l.sum (fun ψ v => v * ψ (Additive.ofMul (idealClass c a))) := hb'.symm
    _ = l.sum (fun ψ v => v * rayValue (rayFourierCharacter c ψ).val a) := by
      apply Finsupp.sum_congr
      intro ψ _
      rw [rayFourierCharacter_rayValue c ψ ha]
    _ = m.sum (fun ξ v => v * rayValue ξ.val a) := by
      exact (Finsupp.sum_mapDomain_index (f := rayFourierCharacter c) (s := l)
        (h := fun (ξ : RayCharacter c) (v : ℂ) => v * rayValue ξ.val a)
        (fun (ξ : RayCharacter c) => zero_mul (rayValue ξ.val a))
        (fun (ξ : RayCharacter c) (u v : ℂ) => add_mul u v (rayValue ξ.val a))).symm
    _ = ∑' ξ : RayCharacter c, m ξ * rayValue ξ.val a := by
      symm
      apply tsum_eq_sum
      intro ξ hξ
      rw [Finsupp.notMem_support_iff.mp hξ, zero_mul]

/-- The exact dispatched finite ray-expansion obligation, with no new premise. -/
theorem second_poisson_ray_expansion_proved : SecondPoissonProof.RayExpansionStatement := by
  intro c hc ξ₁
  let g : RayClass c → ℂ := fun z =>
    rayClassCharacter c ξ₁ z * reciprocityG c hc z⁻¹
  obtain ⟨coeffs, hfinite, hexp⟩ := class_function_ray_expansion c g
  refine ⟨coeffs, hfinite, ?_⟩
  intro a ha
  simpa only [g, rayValue_eq_rayClassCharacter c ξ₁ ha] using hexp a ha

end QRHShort.CloudBatch
