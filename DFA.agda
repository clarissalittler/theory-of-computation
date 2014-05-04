module DFA where

open import Data.Nat
open import Data.Fin
open import Data.Bool
open import Data.Vec
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)
open import Relation.Binary.PropositionalEquality.Core
open import Data.Char

-- so we'll assume that the alphabet is Σ = Char, we'll also is always have q_0 = zero : Fin Q and we're letting
-- the number of states be Q+1
record DFA : Set where
  constructor dfa
  field
    Q : ℕ 
    δ : Fin (suc Q) -> Fin 2 -> Fin (suc Q)
    F : Fin (suc Q) -> Bool

record _¿_ {n : ℕ} (s : Vec (Fin 2) n) (D : DFA) : Set where
  constructor cpath
  field 
    path : Vec (Fin (suc (DFA.Q D))) (suc n)
    startCond : head path ≡ zero
-- it's a bit of an ugly hack, one could even say....it sucks....to have so many instances of suc floating around unnecesarily
    endCond : (DFA.F D (last path)) ≡ true
-- so what we're doing here is the requirement that each step in the sequence of states matches according to the δ
    δCond : (f : Fin n) -> lookup (suc f) path ≡ ((DFA.δ D) (lookup (inject₁ f) path) (lookup f s))
-- is there an easier way to do this?

allDFA : DFA 
allDFA = dfa zero (λ x y → zero) (λ x → true)
-- dfa zero ((λ {zero zero → zero; zero (suc zero) → zero}) (λ x → true))

allDFATest : [] ¿ allDFA
allDFATest = cpath [ zero ] PropEq.refl PropEq.refl (λ ()) -- cute!

allDFATest2 : (zero ∷ (zero ∷ [])) ¿ allDFA
allDFATest2 = cpath (zero ∷ zero ∷ zero ∷ []) PropEq.refl PropEq.refl aux
  where aux : (f : Fin (suc (suc zero))) → lookup (suc f) (zero ∷ zero ∷ zero ∷ []) ≡ DFA.δ allDFA (lookup (inject₁ f) (zero ∷ zero ∷ zero ∷ [])) (lookup f (zero ∷ zero ∷ []))
        aux zero = refl
        aux (suc zero) = refl
        aux (suc (suc ()))

allDFATest2' : (zero ∷ (zero ∷ [])) ¿ allDFA
allDFATest2' = cpath (zero ∷ zero ∷ zero ∷ []) refl refl ((λ {zero → refl ; (suc zero) → refl ; (suc (suc ())) }))
-- yay pattern matching lambdas

