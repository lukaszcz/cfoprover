{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Search where

import Control.Monad.State
import Control.Monad.Logic
import Control.Monad.Error.Class
import Control.Applicative
import Control.Unification
import Control.Unification.IntVar
import Data.List
import Data.Maybe
import Data.Functor
import Data.Bifunctor
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as SymbolMap
import Data.DList (DList)
import qualified Data.DList as DList
import GHC.Base (maxInt)

import Formula

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
    , goals :: [PFormula]
    , spines :: [Spine p]
    , freeSymbol :: Symbol
    }

initProofState :: Int -> ProofState p
initProofState n = ProofState {
    contexts = [emptyContext]
  , goals = []
  , spines = [emptySpine]
  , freeSymbol = n
  }

type ProofMonad p = StateT (ProofState p) (IntBindingT TermF Logic)

instance MonadLogic m => MonadError () (IntBindingT t m) where
    throwError () = empty
    catchError x f = ifte x return (f ())

instance Fallible t v () where
    occursFailure _ _ = ()
    mismatchFailure _ _ = ()

getFreeVar :: ProofMonad p IntVar
getFreeVar = lift freeVar

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

pushGoal :: PFormula -> ProofMonad p ()
pushGoal g = do
  ps <- get
  put ps{goals = g : goals ps}

popGoal :: ProofMonad p ()
popGoal = do
  ps <- get
  put ps{goals = tail (goals ps)}

withSubgoal :: Proof p => Int -> (PFormula -> ProofMonad p a) -> ProofMonad p a
withSubgoal k f = do
  ps <- get
  let (ctxs', ctxs) = splitAt k (contexts ps)
  let (gs', g:gs) = splitAt k (goals ps)
  let (sps', sps) = splitAt k (spines ps)
  put ps{contexts = ctxs, goals = g:gs, spines = sps}
  a <- f g
  ps' <- get
  put ps'{contexts = ctxs' ++ contexts ps'
          , goals = gs' ++ goals ps'
          , spines = sps' ++ spines ps'}
  return a

nextSymbol :: ProofMonad p Symbol
nextSymbol = do
  ps <- get
  let s = freeSymbol ps
  put ps{freeSymbol = s + 1}
  return s

unifyAtoms :: Atom -> Atom -> ProofMonad p ()
unifyAtoms (s1, _) (s2, _) | s1 /= s2 = empty
unifyAtoms (_, args1) (_, args2) = zipWithM_ unify args1 args2

generateTerm :: ProofMonad p Term
generateTerm = return $ tvar 0

resolveVars :: [IntVar] -> ProofMonad p ()
resolveVars = mapM_ (\v -> generateTerm >>= \t -> lift $ bindVar v t)

resolveTermVars :: Term -> ProofMonad p ()
resolveTermVars t = lift (getFreeVars t) >>= resolveVars

minVarDepthInTerm :: SymbolMap Int -> Term -> Int
minVarDepthInTerm m (UTerm (Var x)) = m SymbolMap.! x
minVarDepthInTerm m (UTerm (Fun s args)) =
  foldl' (\d t -> min d (minVarDepthInTerm m t)) (m SymbolMap.! s) args
minVarDepthInTerm _ _ = error "minVarDepthInTerm"

minVarDepth :: Traversable t => SymbolMap Int -> t Term -> ProofMonad p Int
minVarDepth m ts = do
  ts' <- applyBindingsAll ts
  return $ foldl' minDepth maxInt ts'
  where
    minDepth d t = min d (minVarDepthInTerm m t)

{- search' depth depthMap formula = (minDepth, terms, proof) -}
search' :: Proof p => Int -> SymbolMap Int -> PFormula ->
  ProofMonad p (Int, DList Term, p)
search' 0 _ _ = empty
search' n m (PAtom a) = do
  elims <- findElims a
  foldr (\(s,e) acc -> applyElim (n - 1) m s e a <|> acc) empty elims
search' n m a@(PImpl _ _) = intros' n m a
search' n m a@(PForall _ _) = intros' n m a
search' n m (PAnd a b) = do
  (d1, ts1, p1) <- search' n m a
  (d2, ts2, p2) <- search' n m b
  sp <- getSpine
  return (min d1 d2, DList.append ts1 ts2, sp (mkConj p1 p2))
search' n m (POr phi a b) = aux ILeft a <|> aux IRight b
  where
    aux idx c = do
      (d, ts, p) <- search' n m c
      return (d, ts, mkInj idx phi p)
search' n m (PExists s phi a) = do
  evar <- getFreeVar
  let v = UVar evar
  (d, ts, p) <- search' n m (subst [(s,v)] a)
  return (d, ts, mkExIntro s phi v p)

intros' :: Proof p => Int -> SymbolMap Int -> PFormula ->
  ProofMonad p (Int, DList Term, p)
intros' n m a = do
  pushContext
  r <- intros n m a
  popContext
  return r

intros :: Proof p => Int -> SymbolMap Int -> PFormula ->
  ProofMonad p (Int, DList Term, p)
intros n m (PImpl (a, elims) b) = do
  s <- nextSymbol
  addElims s elims
  updateSpine (\sp p -> sp (mkLam s a p))
  intros n (SymbolMap.insert s n m) b
intros n m (PForall s a) = do
  s' <- nextSymbol
  intros n (SymbolMap.insert s' n m) (subst [(s,tvar s')] a)
intros n m x = do
  pushGoal x
  (d, ts, p) <- search' n m x
  popGoal
  sp <- getSpine
  return (d, ts, sp p)

applyElims :: Proof p => Symbol -> Int -> SymbolMap Int -> [Elim PFormula] ->
  ProofMonad p (Int, DList Term, p)
applyElims s n m es = do
  (d, ts, ps) <- foldr (search_subgoal n m) (return (n, DList.empty, [])) es
  return (min d (SymbolMap.findWithDefault d s m), ts, mkElim s ps)
  where
    search_subgoal n m (EApp x) a = do
      (d, ts, p) <- search' n m x
      (d', ts', ps) <- a
      return (min d d', DList.append ts ts', (EApp p):ps)
    search_subgoal _ _ (EAApp t) a = do
      (d, ts, ps) <- a
      return (d, DList.cons t ts, (EAApp t):ps)
    search_subgoal _ _ (EProj i) a = do
      (d, ts, ps) <- a
      return (d, ts, (EProj i):ps)

applyCElims :: Proof p => Int -> SymbolMap Int -> Symbol -> [CElim] ->
  ProofMonad p (Int, DList Term, p)
applyCElims n m s [Elims es] = do
  applyElims s n m es
applyCElims n m s (ECase es idx phi1 es1 phi2 es2 : ces) = do
  (d, ts, p) <- applyElims s n m es
  mapM_ resolveTermVars ts
  dv <- minVarDepth m ts
  let d' = min d dv
  s' <- withSubgoal (n - d') (solveCaseSubgoal d p)
  applyCElims n (SymbolMap.insert s' d' m) s' ces
  where
    solveCaseSubgoal d p g = do
      (_, _, pg) <- search' d m (PImpl (phi2, es2) g)
      s' <- nextSymbol
      updateSpine (\sp p' ->
        case idx of
          ILeft -> sp (mkCase p (mkLam s' phi1 p') pg)
          IRight -> sp (mkCase p pg (mkLam s' phi1 p')))
      addElims s' es1
      return s'
applyCElims n m s (EEx es sa a eas : ces) = do
  (d, ts, p) <- applyElims s n m es
  mapM_ resolveTermVars ts
  dv <- minVarDepth m ts
  let d' = min d dv
  (sa', s') <- withSubgoal (n - d') (insertExElim p)
  addElims s' (map (subst [(sa,tvar sa')]) eas)
  applyCElims n (SymbolMap.insert s' d' (SymbolMap.insert sa' d' m)) s' ces
  where
    insertExElim p _ = do
      sa' <- nextSymbol
      let a' = subst [(sa,tvar sa')] a
      s' <- nextSymbol
      updateSpine (\sp p' -> sp (mkExElim p (mkALam sa' (mkLam s' a' p'))))
      return (sa', s')
applyCElims _ _ _ _ = empty

applyElim :: Proof p => Int -> SymbolMap Int -> Symbol -> Eliminator -> Atom ->
  ProofMonad p (Int, DList Term, p)
applyElim n m s e a = do
  env <- mapM (\s -> getFreeVar >>= \v -> return (s,UVar v)) (evars e)
  let a' = second (map (csubst env)) (target e)
  unifyAtoms a a'
  let es = map (csubst env) (Formula.elims e)
  applyCElims n m s es

search :: Proof p => Int -> Formula -> [p]
search n a =
  observeAll $
  evalIntBindingT $
  evalStateT
    (intros n SymbolMap.empty (compileFormula a) >>= applyTermBindings')
    (initProofState (maxSymbol a + 1))
  where
    applyTermBindings' (_, _, p) =
      applyTermBindings (\t -> resolveTermVars t >> applyBindings t) p
