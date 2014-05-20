module DFA where

import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Error

type States = Int
-- we'll just assume 0 is always the start
data DFA = DFA { nStates :: Int,
                 alphabet :: [Char],
                 delta :: States -> Char -> States,
                 accept :: [States] }

type DFA_MT m a = ErrorT String (StateT (DFA,States) m) a

type DFA_M a = DFA_MT Identity a

processChar :: Char -> DFA_M States
processChar c = do
  a <- gets (alphabet . fst)
  if c `elem` a 
    then do
         d <- gets (delta . fst)
         cs <- gets snd
         let cs' = d cs c
         modify (\ (d,_) -> (d,cs'))
         return cs'
    else throwError "Character not in alphabet"
-- this is really ugly, how do we make this code prettier?

processString :: String -> DFA_M [States]
processString = mapM processChar

-- I guess this is what we get back out of the annoying wrapping things up: control flow ends up being pretty easy, but I still don't like the ugly code here :-/ I'll refactor once I have more examles

processCharIO :: Char -> DFA_MT IO States
processCharIO c = do
  a <- gets (alphabet . fst)
  if c `elem` a 
    then do
         d <- gets (delta . fst)
         cs <- gets snd
         let cs' = d cs c
         modify (\ (d,_) -> (d,cs'))
         liftIO $ putStrLn (show cs')
         return cs'
    else throwError "Character not in alphabet"

processStringIO :: String -> DFA_MT IO [States]
processStringIO = mapM (\s -> liftIO getLine >> processCharIO s)

runDFA_m :: Monad m => DFA -> DFA_MT m a -> m ((Either String a), States)
runDFA_m d m = liftM aux (runStateT (runErrorT m) (d,0))
        where aux (a,(b,c)) = (a,c)
              
runDFA :: DFA -> DFA_M a -> (Either String a,States)
runDFA d m = runIdentity (runDFA_m d m)

testDFA :: DFA
testDFA = DFA 0 "ab" (\ s c -> 0) [0]