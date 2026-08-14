{-# OPTIONS --safe #-}

module HeytingField.Extension.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Ring

open import Cubical.Reflection.RecordEquiv

open import HeytingField.Base
open import HeytingField.Properties

open import HeytingField.Extension.Base

private variable
  ℓ ℓ' ℓ'' ℓ''' ℓ'''' ℓ''''' : Level
  F G H : HeytingField ℓ ℓ'
  E E' E'' : FieldExtension F ℓ'' ℓ'''

module _ (F : HeytingField ℓ ℓ') ((E , F→E , _) : FieldExtension F ℓ'' ℓ''') ((E' , F→E' , _) : FieldExtension F ℓ'''' ℓ''''') where
  record IsExtensionHom (f : HeytingFieldHom E E'): Type (ℓ-max ℓ ℓ'''') where
    constructor makeIsExtensionHom
    field
      presInc : ∀ x → f .fst (F→E x) ≡ F→E' x
    open IsHeytingFieldHom (snd f) public
  
  unquoteDecl isExtensionHomIsoΣ = declareRecordIsoΣ isExtensionHomIsoΣ (quote IsExtensionHom)

  isPropIsExtensionHom : ∀ {f} → isProp (IsExtensionHom f)
  isPropIsExtensionHom = isOfHLevelRetractFromIso 1 isExtensionHomIsoΣ $ isPropΠ λ _ → 
    E' .snd .HeytingFieldStr.is-set _ _

  ExtensionHom : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ'') ℓ''') ℓ'''') ℓ''''')
  ExtensionHom = Σ[ f ∈ HeytingFieldHom E E' ] IsExtensionHom f

  ExtensionEquiv : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓ ℓ'') ℓ''') ℓ'''') ℓ''''')
  ExtensionEquiv = Σ[ f ∈ HeytingFieldEquiv E E' ] IsExtensionHom (f .fst .fst , f .snd)

open IsExtensionHom
open RingEquivs

idExtensionEquiv : ExtensionEquiv F E E
idExtensionEquiv .fst = idFieldEquiv
idExtensionEquiv .snd .presInc x = refl

compExtensionEquiv : ExtensionEquiv F E E' → ExtensionEquiv F E' E'' → ExtensionEquiv F E E''
compExtensionEquiv f g .fst = compFieldEquiv (f .fst) (g .fst)
compExtensionEquiv f g .snd .presInc x = cong (g .fst .fst .fst) (f .snd .presInc x) ∙ g .snd .presInc x

invExtensionEquiv : ExtensionEquiv F E E' → ExtensionEquiv F E' E
invExtensionEquiv f .fst = invFieldEquiv (f .fst)
invExtensionEquiv f .snd .presInc x = cong (invEq (f .fst .fst)) (sym (f .snd .presInc x)) ∙ retEq (f .fst .fst) _

ExtensionAut : (F : HeytingField ℓ ℓ') (E : FieldExtension F ℓ'' ℓ''')
             → Type (ℓ-max (ℓ-max ℓ ℓ'') ℓ''')
ExtensionAut F E = ExtensionEquiv F E E

FieldAutGroup : (F : HeytingField ℓ ℓ') → Group (ℓ-max ℓ ℓ')  
FieldAutGroup F = makeGroup (idFieldEquiv {F = F}) compFieldEquiv invFieldEquiv (isSetHeytingFieldEquiv _ _)
                            (λ _ _ _ → Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) (compEquiv-assoc _ _ _))
                            (λ _ → Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) (compEquivEquivId _))
                            (λ _ → Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) (compEquivIdEquiv _))
                            (λ _ → Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) (invEquiv-is-rinv _))
                            (λ _ → Σ≡Prop (λ _ → isPropIsHeytingFieldHom _ _ _) (invEquiv-is-linv _))

-- It's defined as a subgroup of the group of the automorphism group of its underlying field
ExtensionAutGroup : (F : HeytingField ℓ ℓ') (E : FieldExtension F (ℓ-max ℓ ℓ'') ℓ'') -- Have to slightly reduce level-polymorphism here because subgroups are not polymorphic enough
                  → Group (ℓ-max ℓ ℓ'')
ExtensionAutGroup F Eext@(E , E→F , E→FIsHom) = Subgroup→Group (FieldAutGroup E) asSubgroup
  module ExtensionAutGroup where
    open isSubgroup
    asSubgroup : Subgroup (FieldAutGroup E)
    asSubgroup .fst f .fst = IsExtensionHom F Eext Eext (f .fst .fst , f .snd)
    asSubgroup .fst f .snd = isPropIsExtensionHom _ _ _
    asSubgroup .snd .id-closed .presInc x = refl
    asSubgroup .snd .op-closed {x = f} {y = g} fh gh .presInc x = cong (g .fst .fst) (fh .presInc x) ∙ gh .presInc x
    asSubgroup .snd .inv-closed {x = f} fh .presInc x = cong (invEq (f .fst)) (sym (fh .presInc x)) ∙ retEq (f .fst) (E→F x)
