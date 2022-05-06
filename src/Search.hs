module Search where

import Control.Monad.State
import Data.List
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as SymbolMap

import Logic

type SymbolMap = IntMap

data Context = Context {
      elims :: SymbolMap [Eliminator]
    }

emptyContext :: Context
emptyContext = Context{Search.elims = SymbolMap.empty}

type Spine p = p -> [p] -> p

emptySpine :: Spine p
emptySpine p _ = p

type Subgoal = (Context,PFormula)

data ProofState p = ProofState {
      contexts :: [Context]
    , spines :: [Spine p]
    , subgoals :: [Subgoal] -- subgoals for case expressions
    , freeSymbol :: Symbol
    }
{- invariant: length subgoals = length of the second argument of the
   corresponding spine -}

lookup :: Symbol -> Context -> [Eliminator]
lookup s ctx =
    case SymbolMap.lookup s (Search.elims ctx) of
      Just es -> es
      Nothing -> []

getContexts :: State (ProofState p) [Context]
getContexts = get >>= return . contexts

getSpines :: State (ProofState p) [Spine p]
getSpines = get >>= return . spines

getSpine :: State (ProofState p) (Spine p)
getSpine = get >>= return . head . spines

setSpine :: Spine p -> State (ProofState p) ()
setSpine sp = do
  ps <- get
  put ps{spines = sp : tail (spines ps)}
  return ()

getSubgoals :: State (ProofState p) [Subgoal]
getSubgoals = get >>= return . subgoals

addSubgoal :: Subgoal -> State (ProofState p) ()
addSubgoal g = do
  ps <- get
  put ps{subgoals = g : subgoals ps}

findElims :: Atom -> [Context] -> [Eliminator]
findElims (pred, _) ctxs =
    sortBy (\x y -> compare (cost x) (cost y)) $
    concat $
    zipWith (\c -> map (\e -> e{cost = cost e + c})) [0,5..] $
            map (Search.lookup pred) ctxs

pushContext :: State (ProofState p) ()
pushContext = do
  ps <- get
  put $ ps{contexts = emptyContext : contexts ps, spines = emptySpine : spines ps}
  return ()

popContext :: State (ProofState p) ()
popContext = do
  ps <- get
  put $ ps{contexts = tail (contexts ps), spines = tail (spines ps)}
  return ()

nextSymbol :: State (ProofState p) Symbol
nextSymbol = do
  ps <- get
  let s = freeSymbol ps
  put ps{freeSymbol = s + 1}
  return s

search :: Proof p => PFormula -> State (ProofState p) (Maybe p)
search = undefined
