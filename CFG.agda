module CFG where

open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.String
open import Data.Vec
open import Data.Product

record CFG : Set where
  constructor cfg
  field
    vars : ℕ
    terminals : ℕ
    rules : Fin vars -> (List (Fin vars ⊎ Fin terminals ⊎ ⊤))

{- So what I really need to do here is map CFGs to descriptions. I get that now. That's why everything felt so weird and didn't work. This might make more sense now won't it.


  Maybe there's an easier way of doing this honestly? If I /have/ to use descriptions that feels like major overkill for doing this. On the other hand, descriptions are damn cute. Alright, I'll do it! 
  -}

data Desc : Set₁ where
 `1 : Desc
 `Σ : (S : Set) -> (D : S -> Desc) -> Desc
 `ind× : Desc -> Desc

⟦_⟧ : Desc -> Set -> Set
⟦_⟧ `1 X = ⊤
⟦_⟧ (`Σ S D) X = Σ S (λ s → ⟦ D s ⟧ X)
⟦_⟧ (`ind× D) X = X × ⟦ D ⟧ X

data μ (D : Desc) : Set where
  con : ⟦ D ⟧ (μ D) -> μ D 

-- description tests

NatD : Desc
NatD = `Σ (Fin 2) aux
  where aux : Fin 2 -> Desc
        aux zero = `1
        aux (suc zero) = `ind× `1
        aux (suc (suc ()))

Nat : Set
Nat = μ NatD

zD : Nat
zD = con (zero , tt)

sucD : Nat -> Nat
sucD n = con (suc zero , n , tt)

-- okay, starting to get the hang of this
-- now let's try doing an example that involves a pair

PairD : Set -> Set -> Desc
PairD A B = `Σ A (λ _ → `Σ B (λ _ → `1))

Pair : Set -> Set -> Set
Pair A B = μ (PairD A B)

test : Pair Nat Nat
test = con (zD , zD , tt)

{- daaaaamn, okay, that kinda makes sense, well now the question is how are we going to map all that using CFGs. Well, hell, let's take a stab at it. 

So to start with there needs to be a big ol' outer sigma using the Fin vars, right?

  and crap this is where it gets tricky, right?
 -}

cfgToDesc : CFG -> Desc
cfgToDesc (cfg vars terminals rules) = `Σ (Fin vars) (λ v → listToDesc (rules v))
  where listToDesc : List (Fin vars ⊎ Fin terminals ⊎ ⊤) -> Desc
        listToDesc [] = `1 -- When all you have is induction, everything looks like a case
        listToDesc (inj₁ x ∷ l) = {!!}
        listToDesc (inj₂ (inj₁ x) ∷ l) = {!!} -- nope, don't get it
        listToDesc (inj₂ (inj₂ y) ∷ l) = {!!}
