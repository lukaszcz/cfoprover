{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
module Search where

import Control.Monad.State
import Control.Monad.Logic
import Control.Monad.Error.Class
import Control.Applicative
import qualified Control.Unification as U
import Control.Unification.IntVar
import Data.List
import Data.Maybe
import Data.Functor
import Data.Bifunctor
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.DList (DList)
import qualified Data.DList as DList
import GHC.Base (maxInt)

import Formula

data Context = Context {
      -- 'elims' maps target head symbol ids to:
      -- (context variable symbol, depth of variable, eliminator)
      elims :: IntMap [(Symbol,Eliminator)]
      -- 'params' contains symbol ids of the parameters in the context
    , params :: IntSet
      -- invariant: eliminators in a context contain no free term variables
    }

emptyContext :: Context
emptyContext = Context{Search.elims = IntMap.empty, Search.params = IntSet.empty}

type Spine p = p -> p
{- given a proof for the spine hole, returns a complete proof term -}

emptySpine :: Spine p
emptySpine = id

data ProofState p = ProofState {
      contexts :: [Context]
    , goals :: [PFormula]
    , spines :: [Spine p]
    , depthMaps :: [IntMap Int]
    -- depthMaps: maps symbols to depths at which they were introduced
    , contextDepth :: Int
    -- contextDepth = length contexts - 1
    , freeSymbolId :: Int
    , signature :: Signature
    }

initProofState :: Signature -> ProofState p
initProofState sig = ProofState {
    contexts = [emptyContext]
  , goals = []
  , spines = [emptySpine]
  , depthMaps = [IntMap.empty]
  , contextDepth = 0
  , freeSymbolId = maxSymbolId sig + 1
  , signature = sig
  }

type ProofMonad p = StateT (ProofState p) (IntBindingT TermF Logic)

instance MonadLogic m => MonadError () (IntBindingT t m) where
    throwError () = empty
    catchError x f = ifte x return (f ())

instance U.Fallible t v () where
    occursFailure _ _ = ()
    mismatchFailure _ _ = ()

nextEVar :: ProofMonad p Term
nextEVar = U.UVar <$> lift U.freeVar

lookup :: Symbol -> Context -> [(Symbol,Eliminator)]
lookup s ctx =
    fromMaybe [] (IntMap.lookup (sid s) (Search.elims ctx))

getContexts :: ProofMonad p [Context]
getContexts = get <&> contexts

getContext :: ProofMonad p Context
getContext = get <&> head . contexts

getSpines :: ProofMonad p [Spine p]
getSpines = get <&> spines

getSpine :: ProofMonad p (Spine p)
getSpine = get <&> head . spines

setSpine :: Spine p -> ProofMonad p ()
setSpine sp = do
  ps <- get
  put ps{spines = sp : tail (spines ps)}

updateSpine :: (Spine p -> Spine p) -> ProofMonad p ()
updateSpine f = do
  ps <- get
  put ps{spines = f (head (spines ps)) : tail (spines ps)}

getDepthMap :: ProofMonad p (IntMap Int)
getDepthMap = get <&> head . depthMaps

getDepth :: Int -> ProofMonad p Int
getDepth id = getDepthMap <&> fromJust . IntMap.lookup id

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
    elims' = foldr (\e -> IntMap.insertWith (++) (sid $ fst (target e)) [(s,e)])
                    (Search.elims ctx)
                    es

addElims :: Symbol -> [Eliminator] -> ProofMonad p ()
addElims s elims = do
  ps <- get
  let (ctx:cs) = contexts ps
  put ps{ contexts = addElims' s elims ctx : cs
        , depthMaps =
          IntMap.insert (sid s) (contextDepth ps) (head (depthMaps ps)) : tail (depthMaps ps) }

addParam' :: Symbol -> Context -> Context
addParam' s ctx = ctx{ Search.params = IntSet.insert (sid s) (Search.params ctx) }

addParam :: Symbol -> ProofMonad p ()
addParam s = do
  ps <- get
  let (ctx:cs) = contexts ps
  put ps{ contexts = addParam' s ctx : cs
        , depthMaps =
          IntMap.insert (sid s) (contextDepth ps) (head (depthMaps ps)) : tail (depthMaps ps) }

pushContext :: ProofMonad p ()
pushContext = do
  ps <- get
  put ps{ contexts = emptyContext : contexts ps
        , spines = emptySpine : spines ps
        , depthMaps = head (depthMaps ps) : depthMaps ps
        , contextDepth = contextDepth ps + 1 }

popContext :: ProofMonad p ()
popContext = do
  ps <- get
  put ps{ contexts = tail (contexts ps)
        , spines = tail (spines ps)
        , depthMaps = tail (depthMaps ps)
        , contextDepth = contextDepth ps - 1 }

pushGoal :: PFormula -> ProofMonad p ()
pushGoal g = do
  ps <- get
  put ps{goals = g : goals ps}

popGoal :: ProofMonad p ()
popGoal = do
  ps <- get
  put ps{goals = tail (goals ps)}

withSubgoal :: Proof p => Int -> (PFormula -> ProofMonad p a) -> ProofMonad p a
withSubgoal d f = do
  ps <- get
  let k = contextDepth ps - d
  let (ctxs', ctxs) = splitAt k (contexts ps)
  let (gs', g:gs) = splitAt k (goals ps)
  let (sps', sps) = splitAt k (spines ps)
  let (mps', mps) = splitAt k (depthMaps ps)
  put ps{ contexts = ctxs
        , goals = g:gs
        , spines = sps
        , depthMaps = mps
        , contextDepth = d }
  a <- f g
  ps' <- get
  put ps'{  contexts = ctxs' ++ contexts ps'
          , goals = gs' ++ goals ps'
          , spines = sps' ++ spines ps'
          , depthMaps =
              foldr (\mp mps -> IntMap.union mp (head (depthMaps ps')) : mps)
                (depthMaps ps')
                mps'
          , contextDepth = contextDepth ps }
  return a

nextSymbolNamed :: String -> ProofMonad p Symbol
nextSymbolNamed s = do
  ps <- get
  let id = freeSymbolId ps
  put ps{ freeSymbolId = id + 1 }
  return $ Symbol s id

nextSymbol :: ProofMonad p Symbol
nextSymbol = nextSymbolNamed ""

unifyAtoms :: Atom -> Atom -> ProofMonad p ()
unifyAtoms (s1, _) (s2, _) | s1 /= s2 = empty
unifyAtoms (_, args1) (_, args2) = zipWithM_ U.unify args1 args2

generateTerm :: Int -> ProofMonad p Term
generateTerm n = do
  ctx <- getContext
  IntSet.foldl' (\a c -> return (tfun (Symbol ("_X" ++ show c) c) []) <|> a) cont (params ctx)
  where
    cont =
      if n == 0 then
        empty
      else do
        ps <- get
        let sig = signature ps
        foldl' (build sig) empty (symbols sig)
        where
          build sig a s = do
            let k = fromJust $ IntMap.lookup (sid s) (symbolArity sig)
            args <- replicateM k (generateTerm (n - 1))
            return (tfun s args) <|> a

resolveEVars :: Int -> [IntVar] -> ProofMonad p ()
resolveEVars n = mapM_ (\v -> generateTerm n >>= \t -> lift $ U.bindVar v t)

resolveTermEVars :: Int -> Term -> ProofMonad p ()
resolveTermEVars n t = lift (U.getFreeVars t) >>= resolveEVars n

getMaxDepth :: IntSet -> ProofMonad p Int
getMaxDepth su = do
  mp <- getDepthMap
  return $ IntSet.foldl' (\a x -> max a (fromJust $ IntMap.lookup x mp)) 0 su

checkParamsInTerm :: IntSet -> Term -> ProofMonad p IntSet
checkParamsInTerm su (U.UTerm (Fun s args)) = do
  ps <- get
  let d = contextDepth ps
  let mp = head (depthMaps ps)
  if fromMaybe maxInt (IntMap.lookup (sid s) mp) > d then
    empty
  else
    foldl' (\a x -> a >>= \su -> checkParamsInTerm su x)
          (return $ IntSet.insert (sid s) su)
          args
checkParamsInTerm _ _ = error "checkParamsInTerm"

checkParams :: Traversable t => t Term -> ProofMonad p IntSet
checkParams ts = do
  ts' <- U.applyBindingsAll ts
  foldl' (\a x -> a >>= \su -> checkParamsInTerm su x) (return IntSet.empty) ts'

{- search limit (argument to search') should not be confused with context depth -}
{- search' limit env formula = (symbolsUsed, terms (evars), proof) -}
search' :: Proof p => Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, p)
search' 0 _ _ = empty
search' _ _ (PAtom (s, _)) | s == sBottom = empty
search' n env (PAtom a) = searchElim n env a
search' n env a@(PImpl _ _) = intros' n env a
search' n env a@(PForall _ _) = intros' n env a
search' n env (PAnd a b) = do
  (su1, ts1, p1) <- search' n env a
  (su2, ts2, p2) <- search' n env b
  sp <- getSpine
  return (IntSet.union su1 su2, DList.append ts1 ts2, sp (mkConj p1 p2))
search' n env (POr phi a b) = aux ILeft a <|> aux IRight b
  where
    aux idx c = do
      (su, ts, p) <- search' n env c
      return (su, ts, mkInj idx (subst env phi) p)
search' n env (PExists _ phi a) = do
  v <- nextEVar
  (su, ts, p) <- search' n (v:env) a
  return (su, DList.cons v ts, mkExIntro (subst env phi) v p)

searchElim :: Proof p => Int -> [Term] -> Atom -> ProofMonad p (IntSet, DList Term, p)
searchElim n env a = do
  elims <- findElims a
  foldr (\(s,e) acc -> applyElim (n - 1) s e (subst env a) <|> acc) empty elims

intros' :: Proof p => Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, p)
intros' n env a = do
  pushContext
  (su, ts, p) <- intros n env a
  ctx <- getContext
  mapM_ (resolveTermEVars n) ts
  sut <- checkParams ts
  popContext
  return (IntSet.difference
              (IntSet.difference (IntSet.union su sut)
                    (IntMap.keysSet (Search.elims ctx)))
              (Search.params ctx)
          , DList.empty, p)

intros :: Proof p => Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, p)
intros n env (PImpl (a, elims) b) = do
  s <- nextSymbol
  addElims s (map (subst env) elims)
  updateSpine (\sp p -> sp (mkLam s (subst env a) p))
  intros n env b
intros n env (PForall name a) = do
  s <- nextSymbolNamed name
  addParam s
  updateSpine (\sp p -> sp (mkALam s p))
  intros n (tfun s [] : env) a
intros n env x = do
  pushGoal x
  (su, ts, p) <- searchAfterIntros n env x
  popGoal
  sp <- getSpine
  return (su, ts, sp p)

searchAfterIntros :: Proof p => Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, p)
searchAfterIntros 0 _ _ = empty
searchAfterIntros n env (PAtom a) = do
  es1 <- findElims a
  es2 <- findElims aBottom
  foldr apElim empty (elims es1 es2)
  where
    elims es1 es2 = sortBy (\x y -> compare (cost (snd x)) (cost (snd y))) (es1 ++ es2)
    apElim (s, e) acc | s == sBottom = applyElim (n - 1) s e aBottom <|> acc
    apElim (s, e) acc = applyElim (n - 1) s e (subst env a) <|> acc
searchAfterIntros n env g = search' n env g <|> searchElim n env aBottom

applyElims :: Proof p => Int -> [Term] -> Symbol -> [Elim PFormula] ->
  ProofMonad p (IntSet, DList Term, p)
applyElims n env s es = do
  (sus, ts, ps) <- foldr (search_subgoal . subst env) (return ([], DList.empty, [])) es
  return (IntSet.insert (sid s) (IntSet.unions sus), ts, mkElim s ps)
  where
    search_subgoal (EApp x) a = do
      (su, ts, p) <- search' n [] x
      (sus, ts', ps) <- a
      return (su : sus, DList.append ts ts', EApp p : ps)
    search_subgoal (EAApp t) a = do
      (sus, ts, ps) <- a
      return (sus, DList.cons t ts, EAApp t : ps)
    search_subgoal (EProj i) a = do
      (sus, ts, ps) <- a
      return (sus, ts, EProj i : ps)

fixApplyElims :: Proof p => Int -> [Term] -> Int -> Symbol -> [Elim PFormula]
  -> ProofMonad p ([Term], [Term], Int, p)
fixApplyElims n env k s es = do
  let (vars, env') = splitAt k env
  let env0 = reverse vars
  (su, ts, p) <- applyElims n env0 s es
  mapM_ (resolveTermEVars n) ts
  sut <- checkParams ts
  let su' = IntSet.union su sut
  d <- getMaxDepth su'
  return (env0, env', d, p)

applyCElims :: Proof p => Int -> [Term] -> [Symbol] -> Symbol -> CElims ->
  ProofMonad p (IntSet, DList Term, p)
applyCElims n env _ s (Elims _ es) = do
  applyElims n env s es
applyCElims n env params s (ECase k es idx phi1 es1 phi2 es2 ces) = do
  (env0, env', d, p) <- fixApplyElims n env k s es
  s' <- withSubgoal d (solveCaseSubgoal env0 d p)
  applyCElims n env' params s' (subst env0 ces)
  where
    solveCaseSubgoal env0 d p g = do
      (_, _, pg) <- search' d [] (PImpl (subst env0 phi2, map (subst env0) es2) g)
      s' <- nextSymbol
      updateSpine (\sp p' ->
        case idx of
          ILeft -> sp (mkCase p (mkLam s' (subst env0 phi1) p') pg)
          IRight -> sp (mkCase p pg (mkLam s' (subst env0 phi1) p')))
      addElims s' (map (subst env0) es1)
      return s'
applyCElims n env params s (EEx k es a eas ces) = do
  (env0, env', d, p) <- fixApplyElims n env k s es
  let sa = head params
  let env0' = tvar (sid sa) : env0
  s' <- withSubgoal d (insertExElim sa env0' p)
  addElims s' (map (subst env0') eas)
  applyCElims n (tail env') (tail params) s' (subst env0' ces)
  where
    insertExElim sa env0' p _ = do
      s' <- nextSymbol
      updateSpine (\sp p' ->
        sp (mkExElim p (mkALam sa (mkLam s' (subst env0' a) p'))))
      addParam sa
      return s'

createEVars :: CElims -> ProofMonad p ([Term], [Symbol])
createEVars (Elims k _) = do
  env <- replicateM k nextEVar
  return (env, [])
createEVars (ECase k _ _ _ _ _ _ ces) = do
  env <- replicateM k nextEVar
  (env', params) <- createEVars ces
  return (env ++ env', params)
createEVars (EEx k _ _ _ ces) = do
  env <- replicateM k nextEVar
  s <- nextSymbol
  (env', params) <- createEVars ces
  return (env ++ [tfun s []] ++ env', s : params)

applyElim :: Proof p => Int -> Symbol -> Eliminator -> Atom ->
  ProofMonad p (IntSet, DList Term, p)
applyElim n s e a = do
  vs <- mapM (lift . U.getFreeVars) (snd a)
  -- this is not entirely correct because 'e' might also contain evars
  if null vs then once cont else cont
  where
    cont = do
      (env, params) <- createEVars (Formula.elims e)
      let a' = second (map (subst (reverse env))) (target e)
      unifyAtoms a a'
      applyCElims n env params s (Formula.elims e)

search :: Proof p => Signature -> Int -> Formula -> [p]
search sig depthLimit formula =
  observeAll $
  evalIntBindingT $
  evalStateT
    (intros depthLimit [] (compileFormula formula) >>= applyTermBindings')
    (initProofState sig)
  where
    applyTermBindings' (_, _, p) =
      applyTermBindings (\t -> resolveTermEVars depthLimit t >> U.applyBindings t) p
