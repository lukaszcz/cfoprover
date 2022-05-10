module Search where

import Control.Monad.State
import Control.Monad.Logic
import Control.Applicative
import Control.Unification
import Control.Unification.IntVar
import Data.List
import Data.Maybe
import Data.Functor
import Data.Bifunctor
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as SymbolMap

import Logic

type SymbolMap = IntMap

newtype Context = Context {
      elims :: SymbolMap [(Symbol,Eliminator)]
    }

emptyContext :: Context
emptyContext = Context{Search.elims = SymbolMap.empty}

type Spine p = p -> p
{- given a proof for the spine hole, returns a complete proof term -}

emptySpine :: Spine p
emptySpine = id

data ProofState p = ProofState {
      contexts :: [Context]
    , spines :: [Spine p]
    , freeSymbol :: Symbol
    }
{- invariant: length subgoals = length of the second argument of the
   corresponding spine -}

initProofState :: Int -> ProofState p
initProofState n = ProofState {
    contexts = [emptyContext]
  , spines = [emptySpine]
  , freeSymbol = n
  }

type ProofMonad p = StateT (ProofState p) (IntBindingT TermF Logic)

lookup :: Symbol -> Context -> [(Symbol,Eliminator)]
lookup s ctx =
    fromMaybe [] (SymbolMap.lookup s (Search.elims ctx))

getContexts :: ProofMonad p [Context]
getContexts = get <&> contexts

getContext :: ProofMonad p Context
getContext = get <&> (head . contexts)

getSpines :: ProofMonad p [Spine p]
getSpines = get <&> spines

getSpine :: ProofMonad p (Spine p)
getSpine = get <&> (head . spines)

setSpine :: Spine p -> ProofMonad p ()
setSpine sp = do
  ps <- get
  put ps{spines = sp : tail (spines ps)}

updateSpine :: (Spine p -> Spine p) -> ProofMonad p ()
updateSpine f = do
  ps <- get
  put ps{spines = f (head (spines ps)) : tail (spines ps)}

findElims' :: Atom -> [Context] -> [(Symbol,Eliminator)]
findElims' (pred, _) ctxs =
  sortBy (\x y -> compare (cost (snd x)) (cost (snd y))) $
  concat $
  zipWith (\c -> map (\(s,e) -> (s,e{cost = cost e + c}))) [0,5..] $
  map (Search.lookup pred) ctxs

findElims :: Atom -> ProofMonad p [(Symbol,Eliminator)]
findElims a = getContexts <&> findElims' a

addElims' :: Symbol -> [Eliminator] -> Context -> Context
addElims' s es ctx = ctx{Search.elims = elims'}
  where
    elims' = foldr (\e -> SymbolMap.insertWith (++) (fst (target e)) [(s,e)])
                    (Search.elims ctx)
                    es

addElims :: Symbol -> [Eliminator] -> ProofMonad p ()
addElims s elims = do
  ps <- get
  let (ctx:cs) = contexts ps
  put ps{contexts = addElims' s elims ctx : cs}

pushContext :: ProofMonad p ()
pushContext = do
  ps <- get
  put ps{contexts = emptyContext : contexts ps, spines = emptySpine : spines ps}

popContext :: ProofMonad p ()
popContext = do
  ps <- get
  put ps{contexts = tail (contexts ps), spines = tail (spines ps)}

nextSymbol :: ProofMonad p Symbol
nextSymbol = do
  ps <- get
  let s = freeSymbol ps
  put ps{freeSymbol = s + 1}
  return s

unifyAtoms :: Atom -> Atom -> ProofMonad p p
unifyAtoms (s1, _) (s2, _) | s1 /= s2 = empty
unifyAtoms (_, args1) (_, args2) = empty

{- search' depth depthMap formula = (minDepth, proof) -}
search' :: Proof p => Int -> SymbolMap Int -> PFormula -> ProofMonad p (Int, p)
search' 0 _ _ = empty
search' n m (PAtom a) = do
  elims <- findElims a
  foldr (\(s,e) acc -> applyElim (n - 1) m s e a <|> acc) empty elims
search' n m a@(PImpl _ _) = intros n m a
search' n m a@(PAnd _ _) = intros n m a
search' n m a@(PForall _ _) = intros n m a
search' n m (POr phi a b) = aux ILeft a <|> aux IRight b
  where
    aux idx c = do
      updateSpine (\sp p -> sp (mkInj idx phi p))
      search' n m c
search' n m (PExists s phi a) = do
  evar <- lift freeVar
  let v = UVar evar
  updateSpine (\sp p -> sp (mkExIntro s phi v p))
  search' n m (subst [(s,v)] a)

intros :: Proof p => Int -> SymbolMap Int -> PFormula -> ProofMonad p (Int, p)
intros n m (PImpl (a, elims) b) = do
  s <- nextSymbol
  addElims s elims
  updateSpine (\sp p -> sp (mkLam s a p))
  intros n (SymbolMap.insert s n m) b
intros n m (PAnd a b) = do
  pushContext
  (d1, pa) <- intros n m a
  popContext
  updateSpine (\sp p -> sp (mkConj pa p))
  (d2, p) <- intros n m b
  return (min d1 d2, p)
intros n m (PForall s a) = do
  s' <- nextSymbol
  intros n (SymbolMap.insert s' n m) (subst [(s,tvar s')] a)
intros n m x = search' n m x

applyCElims :: Proof p => Int -> SymbolMap Int -> Symbol -> [CElim] ->
  ProofMonad p (Int, [p])
applyCElims n m s [Elims es] = empty
applyCElims n m s (ECase es idx : ces) = empty
applyCElims n m s (EEx es s' : ces) = empty
applyCElims _ _ _ _ = empty

applyElim :: Proof p => Int -> SymbolMap Int -> Symbol -> Eliminator -> Atom ->
  ProofMonad p (Int, p)
applyElim n m s e a = do
  env <- mapM (\s -> lift freeVar >>= \v -> return (s,UVar v)) (evars e)
  let a' = second (map (csubst env)) (target e)
  unifyAtoms a a'
  let es = map (csubst env) (Logic.elims e)
  applyCElims n m s es
  empty

search :: Proof p => Int -> Formula -> [p]
search n a =
  observeAll $
  evalIntBindingT $
  evalStateT (snd <$> intros n SymbolMap.empty (compileFormula a)) (initProofState 0)
