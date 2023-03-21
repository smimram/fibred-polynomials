{-# OPTIONS --rewriting --without-K --allow-unsolved-metas #-}

open import HoTT
open import Polynomial
open import Bicategory

Pol : Bicategory
Bicategory.obj Pol = Type₀
Bicategory.hom Pol I J = I ↝ J
Bicategory._⊗_ Pol P Q = P · Q
Bicategory.assoc Pol P Q R = Poly-ua (assoc-≃ P Q R)
Bicategory.id Pol = Id
Bicategory.unit-l Pol P = Poly-ua (unit-l-≃ P)
Bicategory.unit-r Pol P = Poly-ua (unit-r-≃ P)
Bicategory.pentagon Pol P Q R S = {!Poly-ua₂ ? ? ?!}
-- Agda apparently loops when we try to fill this in...
Bicategory.triangle Pol {I} {J} {K} P Q = {!!} ∙ Poly-ua₂ {!!} {!(unit-r-≃ P) ≃₁-· ?!} (triangle P Q) ∙ {!!} 
Bicategory.homs-gpd Pol I J = {!!}
Bicategory.univ Pol = {!!}
