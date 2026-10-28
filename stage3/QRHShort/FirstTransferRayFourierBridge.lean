import QRHShort.FirstTransferRayFourier
import QRHShort.ArithmeticStatements
import QRHShort.PrimaryGenerator

/-! Realize the finite character basis as the literal ray characters at the
frozen arithmetic modulus.  The evaluation identity holds at all ideals
outside the excluded set, without a reciprocity or squarefreeness premise. -/

noncomputable section

open Classical UniqueFactorizationMonoid
open scoped BigOperators

namespace QRHShort.FirstTransferRayFourier

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

/-- The Fourier coefficient bound is uniform in every bounded input function.
The finite family of literal ray characters is fixed by the arithmetic context. -/
theorem exists_uniform_ray_expansion (c : ArithmeticContext) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g : RayClass c → ℂ, (∀ x, ‖g x‖ ≤ 1) →
      ∃ l : RayFourierIndex c → ℂ,
        (∑ ψ : RayFourierIndex c, ‖l ψ‖) ≤ B ∧
        ∀ a b : Ideal O, Outside c.S a → Outside c.S b →
          g (idealClass c a * (idealClass c b)⁻¹) =
            ∑ ψ : RayFourierIndex c,
              l ψ * rayValue (rayFourierCharacter c ψ).val a *
                star (rayValue (rayFourierCharacter c ψ).val b) := by
  let : Fintype (RayClass c) := rayClassFintype c
  obtain ⟨B, hB, h⟩ := exists_uniform_expansion (Additive (RayClass c))
  refine ⟨B, hB, ?_⟩
  intro g hg
  obtain ⟨l, hl, hexp⟩ := h (fun x => g x.toMul) (fun x => hg x.toMul)
  refine ⟨l, hl, ?_⟩
  intro a b ha hb
  have heq := hexp (Additive.ofMul (idealClass c a)) (Additive.ofMul (idealClass c b))
  change g (idealClass c a / idealClass c b) = _ at heq
  rw [div_eq_mul_inv] at heq
  simpa only [rayFourierCharacter_rayValue c _ ha,
    rayFourierCharacter_rayValue c _ hb] using heq

end QRHShort.FirstTransferRayFourier
