import QRHShort.FirstTransferRayFourierBridge

/-! Descend any of the frozen ray characters to the finite ray-class group.
Fourier expansion of its product with an arbitrary bounded class function
then has a coefficient bound independent of both factors. -/

noncomputable section

open Classical
open scoped BigOperators

namespace QRHShort.FirstTransferRayFourier

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

theorem norm_rayClassCharacter (c : ArithmeticContext) (ξ : RayCharacter c)
    (z : RayClass c) : ‖rayClassCharacter c ξ z‖ = 1 := by
  let : Finite (RayClass c) := rayClassFinite c
  exact ((rayClassCharacter c ξ).isOfFinOrder (isOfFinOrder_of_finite z)).norm_eq_one

theorem rayClassCharacter_mul_inv (c : ArithmeticContext) (ξ : RayCharacter c)
    (x y : RayClass c) :
    rayClassCharacter c ξ (x * y⁻¹) =
      rayClassCharacter c ξ x * star (rayClassCharacter c ξ y) := by
  have hinv : rayClassCharacter c ξ y⁻¹ = (rayClassCharacter c ξ y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, hinv, Complex.inv_eq_conj (norm_rayClassCharacter c ξ y)]
  rfl

/-- One constant works simultaneously for every original ray character and
every bounded class function.  The expanded characters remain the same fixed
finite family from `exists_uniform_ray_expansion`. -/
theorem exists_uniform_twisted_ray_expansion (c : ArithmeticContext) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ : RayCharacter c, ∀ G : RayClass c → ℂ,
      (∀ z, ‖G z‖ ≤ 1) →
      ∃ l : RayFourierIndex c → ℂ,
        (∑ ψ : RayFourierIndex c, ‖l ψ‖) ≤ B ∧
        ∀ a b : Ideal O, Outside c.S a → Outside c.S b →
          rayValue ξ.val a * star (rayValue ξ.val b) *
            G (idealClass c a * (idealClass c b)⁻¹) =
            ∑ ψ : RayFourierIndex c,
              l ψ * rayValue (rayFourierCharacter c ψ).val a *
                star (rayValue (rayFourierCharacter c ψ).val b) := by
  obtain ⟨B, hB, hexp⟩ := exists_uniform_ray_expansion c
  refine ⟨B, hB, ?_⟩
  intro ξ G hG
  let g : RayClass c → ℂ := fun z => rayClassCharacter c ξ z * G z
  have hg : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    simpa only [g, norm_mul, norm_rayClassCharacter, one_mul] using hG z
  obtain ⟨l, hl, h⟩ := hexp g hg
  refine ⟨l, hl, ?_⟩
  intro a b ha hb
  simpa only [g, rayClassCharacter_mul_inv, rayValue_eq_rayClassCharacter c ξ ha,
    rayValue_eq_rayClassCharacter c ξ hb] using h a b ha hb

end QRHShort.FirstTransferRayFourier
