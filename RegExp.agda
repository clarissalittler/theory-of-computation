module RegExp where

open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Data.List hiding (_++_)
open import Data.String
open import Data.Char

data RegExp : Set where
  <_> : Char -> RegExp
  ⊥ : RegExp
  ε : RegExp
  _∘_ : RegExp -> RegExp -> RegExp
  _∪_ : RegExp -> RegExp -> RegExp
  _* : RegExp -> RegExp

data _¿_ : String -> RegExp -> Set where
  matchChar : (a : Char) ->  fromList [ a ] ¿ < a >
  matchEpsilon : "" ¿ ε
  matchUnion₁ : ∀ {l} {R₁ R₂} -> l ¿ R₁ -> l ¿ (R₁ ∪ R₂)
  matchUnion₂ : ∀ {l} {R₁ R₂} -> l ¿ R₂ ->  l ¿ (R₁ ∪ R₂)
  matchConcat : ∀ {R₁ R₂ l₁ l₂} -> l₁ ¿ R₁ -> l₂ ¿ R₂ -> (l₁ ++ l₂) ¿ (R₁ ∘ R₂) 
  matchStar₁ : ∀ {R} -> "" ¿ R *
  matchStar₂ : ∀ {R} {l₁ l₂} -> l₁ ¿ R -> l₂ ¿ R * -> (l₁ ++ l₂) ¿ (R *)

-- these are the matching rules for regular expressions, now let's try some examples

ex2 : "0" ¿ < '0' >
ex2 = matchChar '0'

ex1 : "01" ¿ (< '0' > ∘ ( < '1' > ∪ < '0' > ))
ex1 = matchConcat (matchChar '0') (matchUnion₁ (matchChar '1'))

ex3 : "000" ¿ (< '0' > *)
ex3 = matchStar₂ (matchChar '0') (matchStar₂ (matchChar '0') (matchStar₂ (matchChar '0') matchStar₁))

ex4 : "" ¿ (⊥ *)
ex4 = matchStar₁

