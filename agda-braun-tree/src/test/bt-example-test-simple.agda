module test.bt-example-test-simple where

open import Data.stlib.bt-sum
open import Data.stlib.bt-eq

import Data.braun-tree-simple

open Data.braun-tree-simple

postulate
 a : A

data₁ : BraunTree 0
data₁ = empty

data₂ : BraunTree 1
data₂ = node a
               empty
               empty
               (inj₁ refl)

data₃ : BraunTree 2
data₃ = node a
               (node a
                 empty
                 empty
                 (inj₁ refl))
               empty
               (inj₂ refl)
               
data₄ : BraunTree 4
data₄ = node a 
               (node a
                        (node a
                                 empty
                                 empty
                                 (inj₁ refl))
                        empty
                        (inj₂ refl))
               (node a
                        empty
                        empty
                        (inj₁ refl))
               (inj₂ refl)

insert₁ : BraunTree 2
insert₁ = btInsert a
                 (btInsert a empty) 

insert₂ : BraunTree 1
insert₂ = btInsert a
                 empty

insert₃ : BraunTree 3
insert₃ = btInsert a
                 data₃

insert₄ : BraunTree 2
insert₄ = btInsert a
                 data₂
