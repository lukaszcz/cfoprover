{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveFoldable #-}
module Search(search, searchIter, Options(..), defaultOptions) where

import Control.Monad.State
import Control.Monad.Logic
import Control.Monad.Error.Class
import Control.Monad.Reader
import Control.Applicative
import qualified Control.Unification as U
import Control.Unification.IntVar
import Data.List
import Data.Maybe
import Data.Functor
import Data.Bifunctor
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.DList (DList)
import qualified Data.DList as DList
import GHC.Base (maxInt)

import Types

{------------------------------------}
{- search options -}

data Options = Options {
    optComplete :: Bool
  , optMemoizeThreshold :: Int
  , optMemGen :: Bool
  , optMemGenMaxSymbols :: Int
}

defaultOptions :: Options
defaultOptions = Options {
    optComplete = False
  , optMemoizeThreshold = 100
  , optMemGen = True
  , optMemGenMaxSymbols = 10
}

{------------------------------------}
{- optimized formula representation -}

data CElims
  = Elims Int [Elim PFormula]
  | ECase Int [Elim PFormula] Idx Formula [Eliminator] Formula [Eliminator] CElims
  | EEx String Int [Elim PFormula] Formula [Eliminator] CElims
  -- The Int argument is the number of universal quantifiers before, e.g.,
  -- forall x y . Q(x,y) -> forall z P(x,z) \/ forall z P(y,z) has two

data Eliminator = Eliminator
  { target :: Atom,
    elims :: CElims,
    bindersNum :: Int,
    cost :: Int
  }

data PFormula
  = PAtom Atom
  | PImpl (Formula, [Eliminator]) PFormula
  | PAnd PFormula PFormula
  | POr Formula PFormula PFormula -- the first argument is the original disjunction
  | PForall String PFormula
  | PExists String Formula PFormula -- the second argument is the original existential

instance Substitutable CElims where
  nsubst n env (Elims k es) = Elims k (map (nsubst (n + k) env) es)
  nsubst n env (ECase k es i a eas b ebs cs) =
    ECase
      k
      (map (nsubst (n + k) env) es)
      i
      (nsubst (n + k) env a)
      (map (nsubst (n + k) env) eas)
      (nsubst (n + k) env b)
      (map (nsubst (n + k) env) ebs)
      (nsubst (n + k) env cs)
  nsubst n env (EEx s k es a eas cs) =
    EEx
      s
      k
      (map (nsubst (n + k) env) es)
      (nsubst (n + k + 1) env a)
      (map (nsubst (n + k + 1) env) eas)
      (nsubst (n + k + 1) env cs)

instance Substitutable Eliminator where
  nsubst n env e =
    e{  target = nsubst (n + bindersNum e) env (target e)
      , elims = nsubst n env (elims e) }

instance Substitutable PFormula where
  nsubst n env (PAtom a) = PAtom $ nsubst n env a
  nsubst n env (PImpl (phi, elims) a) =
    PImpl (nsubst n env phi, map (nsubst n env) elims) (nsubst n env a)
  nsubst n env (PAnd a b) = PAnd (nsubst n env a) (nsubst n env b)
  nsubst n env (POr phi a b) = POr (nsubst n env phi) (nsubst n env a) (nsubst n env b)
  nsubst n env (PForall s a) = PForall s (nsubst (n + 1) env a)
  nsubst n env (PExists s phi a) = PExists s (nsubst n env phi) (nsubst (n + 1) env a)

prependElim :: Elim PFormula -> CElims -> CElims
prependElim e (Elims k es) = Elims k (shift k e : es)
prependElim e (ECase k es idx a1 es1 a2 es2 elims) = ECase k (shift k e : es) idx a1 es1 a2 es2 elims
prependElim e (EEx s k es a eas elims) = EEx s k (shift k e : es) a eas elims

prependForallElim :: CElims -> CElims
prependForallElim (Elims k es) = Elims (k + 1) (EAApp (tvar k) : es)
prependForallElim (ECase k es idx a1 es1 a2 es2 elims) = ECase (k + 1) (EAApp (tvar k) : es) idx a1 es1 a2 es2 elims
prependForallElim (EEx s k es a eas elims) = EEx s (k + 1) (EAApp (tvar k) : es) a eas elims

compileFormula :: Formula -> PFormula
compileFormula (Atom a) = PAtom a
compileFormula (Impl a b) = PImpl (a, compileElims a) (compileFormula b)
compileFormula (And a b) = PAnd (compileFormula a) (compileFormula b)
compileFormula phi@(Or a b) = POr phi (compileFormula a) (compileFormula b)
compileFormula (Forall s a) = PForall s (compileFormula a)
compileFormula phi@(Exists s a) = PExists s phi (compileFormula a)

compileAtomElims :: Atom -> [Eliminator]
compileAtomElims a = [Eliminator {target = a, elims = Elims 0 [], bindersNum = 0, cost = 0}]

compileImplElims :: Formula -> [Eliminator] -> [Eliminator]
compileImplElims phi =
  map (\e -> e{ elims = prependElim (EApp (compileFormula phi)) (elims e)
              , cost = cost e + 10 })

compileForallElims :: [Eliminator] -> [Eliminator]
compileForallElims =
  map (\e -> e{ elims = prependForallElim (elims e)
              , bindersNum = bindersNum e + 1
              , cost = cost e
                  + if any (varOccurs (bindersNum e)) (snd (target e)) then 1 else 5 })

compileElims :: Formula -> [Eliminator]
compileElims (Atom a) = compileAtomElims a
compileElims (Impl a b) = compileImplElims a (compileElims b)
compileElims (And a b) =
  map (\e -> e {elims = prependElim (EProj ILeft) (elims e)}) (compileElims a)
    ++ map (\e -> e {elims = prependElim (EProj IRight) (elims e)}) (compileElims b)
compileElims (Or a b) =
  map (\e -> e{ elims = ECase 0 [] ILeft a eas b ebs (elims e)
              , cost = cost e + 10 })
      eas
    ++
  map (\e -> e{ elims = ECase 0 [] IRight b ebs a eas (elims e)
              , cost = cost e + 10 })
      ebs
  where
    eas = compileElims a
    ebs = compileElims b
compileElims (Forall _ a) = compileForallElims (compileElims a)
compileElims (Exists s a) =
  map (\e -> e {elims = EEx s 0 [] a eas (elims e), bindersNum = bindersNum e + 1}) eas
  where
    eas = compileElims a

decompileFormula :: PFormula -> Formula
decompileFormula (PAtom a) = Atom a
decompileFormula (PImpl (phi, _) a) = Impl phi (decompileFormula a)
decompileFormula (PAnd a b) = And (decompileFormula a) (decompileFormula b)
decompileFormula (POr a _ _) = a
decompileFormula (PForall s a) = Forall s (decompileFormula a)
decompileFormula (PExists _ a _) = a

instance Show PFormula where
  showsPrec d x = showsPrec d (decompileFormula x)

{--------------------------------------------------------------------------------}
{- proof monad -}

data Context = Context {
      -- 'cElims' maps target head symbol ids to:
      -- (context variable symbol, eliminator)
      cElims :: IntMap [(Symbol,Eliminator)]
      -- 'cParams' contains symbol ids of the parameters in the context
    , cParams :: IntSet
      -- 'cFormulas' contains the formulas in the context (from which the
      -- eliminators are created)
    , cFormulas :: HashSet Formula
      -- 'cDecls' maps context variable symbol ids to the declarations
    , cDecls :: IntMap (Symbol, Formula)
      -- invariant: formulas and eliminators in a context contain no free term
      -- variables (but may contain uninstantiated evars)
    }

emptyContext :: Context
emptyContext = Context{ cElims = IntMap.empty
                      , cParams = IntSet.empty
                      , cFormulas = HashSet.empty
                      , cDecls = IntMap.empty }

{- given a proof for the spine hole, returns a complete proof term -}
type Spine p = p -> p

emptySpine :: Spine p
emptySpine = id

data ProofState p = ProofState {
      contexts :: [Context]
    , goals :: [PFormula]
    , spines :: [Spine p]
    , caseAtoms :: [HashSet (Symbol, Atom)]
    -- depthMaps: maps symbols to depths at which they were introduced
    , depthMaps :: [IntMap Int]
    -- contextDepth = length contexts
    , contextDepth :: Int
    , freeSymbolId :: Int
    , signature :: Signature
    }

initProofState :: Signature -> ProofState p
initProofState sig = ProofState {
    contexts = []
  , goals = []
  , spines = []
  , caseAtoms = []
  , depthMaps = []
  , contextDepth = 0
  , freeSymbolId = maxSymbolId sig + 1
  , signature = sig
  }

data EList e a = ENil e | ECons a (EList e a) deriving (Foldable)

type ELogic e = LogicT (Reader e)

observeE :: Monoid e => ELogic e a -> Either e [a]
observeE lt =
  case runReader (unLogicT lt (\a f -> reader (ECons a . runReader f)) (reader ENil)) mempty of
    ENil e -> Left e
    l -> Right $ foldr (:) [] l

failE :: Monoid e => e -> ELogic e a
failE e = LogicT $ \_ fk -> reader (\e' -> runReader fk $! (e <> e'))

instance Semigroup Bool where
  (<>) = (||)

instance Monoid Bool where
  mempty = False

type ProofMonad p = StateT (ProofState p) (IntBindingT TermF (ELogic Bool))

instance MonadLogic m => MonadError () (IntBindingT t m) where
    throwError () = empty
    catchError x f = ifte x return (f ())

instance U.Fallible t v () where
    occursFailure _ _ = ()
    mismatchFailure _ _ = ()

failDepth :: ProofMonad p a
failDepth = lift $ lift $ failE True

nextEVar :: ProofMonad p Term
nextEVar = U.UVar <$> lift U.freeVar

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

findElims' :: Atom -> [Context] -> [(Symbol,Eliminator)]
findElims' (pred, _) ctxs =
  sortBy (\x y -> compare (cost (snd x)) (cost (snd y))) $
  concat $
  zipWith (\c -> map (\(s,e) -> (s,e{cost = cost e + c}))) [0,5..] $
  map (fromMaybe [] . IntMap.lookup (sid pred) . cElims) ctxs

findElims :: Atom -> ProofMonad p [(Symbol,Eliminator)]
findElims a = getContexts <&> findElims' a

addElims' :: Symbol -> Formula -> [Eliminator] -> Context -> Context
addElims' s phi es ctx = ctx{cElims = elims', cDecls = decls'}
  where
    elims' = foldr (\e -> IntMap.insertWith (++) (sid $ fst (target e)) [(s,e)])
                    (cElims ctx)
                    es
    decls' = IntMap.insert (sid s) (s, phi) (cDecls ctx)

addElims :: Symbol -> Formula -> [Eliminator] -> ProofMonad p ()
addElims s phi elims = do
  ps <- get
  let (ctx:cs) = contexts ps
  put ps{ contexts = addElims' s phi elims ctx : cs
        , depthMaps =
          IntMap.insert (sid s) (contextDepth ps) (head (depthMaps ps)) : tail (depthMaps ps) }

addParam' :: Symbol -> Context -> Context
addParam' s ctx = ctx{ cParams = IntSet.insert (sid s) (cParams ctx) }

addParam :: Symbol -> ProofMonad p ()
addParam s = do
  ps <- get
  let (ctx:cs) = contexts ps
  put ps{ contexts = addParam' s ctx : cs
        , depthMaps =
          IntMap.insert (sid s) (contextDepth ps) (head (depthMaps ps)) : tail (depthMaps ps) }

getParams :: ProofMonad p IntSet
getParams = IntSet.unions . map cParams <$> getContexts

findDecls :: IntSet -> ProofMonad p [(Symbol, Formula)]
findDecls su = do
  ctxs <- getContexts
  return $ IntSet.foldl' (addDecl ctxs) [] su
  where
    addDecl ctxs a sid =
      foldl' (\a ctx -> case IntMap.lookup sid (cDecls ctx) of
                          Just x -> x : a
                          Nothing -> a)
            a
            ctxs

pushContext :: ProofMonad p ()
pushContext = do
  ps <- get
  put ps{ contexts = emptyContext : contexts ps
        , spines = emptySpine : spines ps
        , caseAtoms = HashSet.empty : caseAtoms ps
        , depthMaps =
          if null (depthMaps ps) then [IntMap.empty] else head (depthMaps ps) : depthMaps ps
        , contextDepth = contextDepth ps + 1 }

popContext :: ProofMonad p ()
popContext = do
  ps <- get
  put ps{ contexts = tail (contexts ps)
        , spines = tail (spines ps)
        , caseAtoms = tail (caseAtoms ps)
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
  let (cas', cas) = splitAt k (caseAtoms ps)
  let (mps', mps) = splitAt k (depthMaps ps)
  put ps{ contexts = ctxs
        , goals = g:gs
        , spines = sps
        , caseAtoms = cas
        , depthMaps = mps
        , contextDepth = d }
  a <- f g
  ps' <- get
  put ps'{  contexts = ctxs' ++ contexts ps'
          , goals = gs' ++ goals ps'
          , spines = sps' ++ spines ps'
          , caseAtoms = cas' ++ caseAtoms ps'
          , depthMaps =
              foldr (\mp mps -> IntMap.union mp (head (depthMaps ps')) : mps)
                (depthMaps ps')
                mps'
          , contextDepth = contextDepth ps }
  return a

applyBindingsInAtom :: Atom -> ProofMonad p Atom
applyBindingsInAtom (s, args) = do
  args' <- mapM U.applyBindings args
  return (s, args')

checkCase :: Symbol -> Atom -> ProofMonad p ()
checkCase s a = do
  a' <- applyBindingsInAtom a
  ps <- get
  let (set:sets) = caseAtoms ps
  if HashSet.member (s, a') set then
    empty
  else
    put ps{caseAtoms = HashSet.insert (s, a') set : sets}

isInContext :: Formula -> ProofMonad p Bool
isInContext phi = do
  phi' <- mapAtomsM (\ _ _ -> applyBindingsInAtom) phi
  any (HashSet.member phi' . cFormulas) <$> getContexts

addToContext :: Formula -> ProofMonad p Bool
addToContext phi = do
  phi' <- mapAtomsM (\ _ _ -> applyBindingsInAtom) phi
  ps <- get
  if any (HashSet.member phi' . cFormulas) (contexts ps) then
    return False
  else do
    let (ctx:cs) = contexts ps
    put ps{ contexts = add phi' ctx : cs }
    return True
    where
      add phi' ctx = ctx{ cFormulas = HashSet.insert phi' (cFormulas ctx) }

nextSymbolNamed :: String -> ProofMonad p Symbol
nextSymbolNamed s = do
  ps <- get
  let id = freeSymbolId ps
  put ps{ freeSymbolId = id + 1 }
  return $ Symbol s id

nextSymbol :: ProofMonad p Symbol
nextSymbol = nextSymbolNamed ""

{--------------------------------------------------------------------------------}
{- terms & parameters -}

unifyAtoms :: Atom -> Atom -> ProofMonad p ()
unifyAtoms (s, args1) (s', args2) | s == s' = zipWithM_ U.unify args1 args2
unifyAtoms _ _ = empty

generateTerm :: Int -> ProofMonad p Term
generateTerm n = do
  params <- getParams
  IntSet.foldl' (\a c -> return (tfun (Symbol ("_c" ++ show c) c) []) <|> a)
    (return (tfun (Symbol "_c" (-1)) []) <|> cont)
    params
  where
    cont =
      if n == 0 then
        failDepth
      else do
        ps <- get
        let sig = signature ps
        foldl' (build sig) empty (functionSymbols sig)
        where
          build sig a s = do
            let k = fromJust $ IntMap.lookup (sid s) (symbolArity sig)
            args <- replicateM k (generateTerm (n - 1))
            return (tfun s args) <|> a

resolveTermEVars :: Int -> Term -> ProofMonad p ()
resolveTermEVars n t = lift (U.getFreeVars t) >>= \v -> resolveEVars n v
  where
    resolveEVars n = mapM_ (\v -> generateTerm n >>= \t -> lift $ U.bindVar v t)

-- returns the set of all symbols occurring in the terms
checkParams :: Traversable t => t Term -> ProofMonad p IntSet
checkParams ts = do
  ts' <- U.applyBindingsAll ts
  foldl' (\a x -> a >>= \su -> checkParamsInTerm su x) (return IntSet.empty) ts'
  where
    checkParamsInTerm :: IntSet -> Term -> ProofMonad p IntSet
    checkParamsInTerm su (U.UTerm (Fun s args)) = do
      ps <- get
      let d = contextDepth ps
      let mp = head (depthMaps ps)
      if sid s > maxSymbolId (signature ps) &&
          fromMaybe maxInt (IntMap.lookup (sid s) mp) > d then
        empty
      else
        foldl' (\a x -> a >>= \su -> checkParamsInTerm su x)
              (return $ IntSet.insert (sid s) su)
              args
    checkParamsInTerm _ _ = error "checkParamsInTerm"

getMaxDepth :: IntSet -> ProofMonad p Int
getMaxDepth su = do
  mp <- getDepthMap
  return $ IntSet.foldl' (\a x -> max a (fromMaybe 0 (IntMap.lookup x mp))) 1 su

{--------------------------------------------------------------------------------}
{- proof memoization -}

memoizeProof :: Proof p => Options -> Atom -> IntSet -> DList Term -> p -> ProofMonad p (IntSet, DList Term, Int, p)
memoizeProof opts a su ts p = do
  sut <- checkParams ts
  let su' = IntSet.union su sut
  d <- getMaxDepth su'
  if d > 1 && optMemGen opts then do
    decls <- findDecls su'
    mp <- getDepthMap
    let decls' = filter (\(s,_) -> fromMaybe maxInt (IntMap.lookup (sid s) mp) > 1) decls
    if length decls' <= optMemGenMaxSymbols opts then do
      -- get evars in decls
      vs <- foldl' (\acc (_, phi) -> foldAtoms (\a acc -> liftA2 (++) (lift $ U.getFreeVarsAll (snd a)) acc) acc phi) (pure []) decls'
      if null vs then do
        -- get ids of symbols in decls
        sut' <- foldl'
              (\acc (_, phi) ->
                foldAtoms
                  (\a acc -> acc >>= \su -> U.applyBindingsAll (snd a) >>= \args ->
                    return $ foldl' (flip extractSyms) (IntSet.insert (sid (fst a)) su) args)
                  acc phi)
              (return IntSet.empty)
              decls'
        let su'' = IntSet.union su' sut'
        params <- IntSet.intersection su'' <$> getParams
        let params' = IntSet.filter (\id -> fromMaybe maxInt (IntMap.lookup id mp) > 1) params
        let p' = IntSet.foldl' (\p sid -> mkALam (Symbol "" sid) p) (foldl' (\p (s, phi) -> mkLam s phi p) p decls') params'
        let phi' = IntSet.foldl' (\a sid -> Forall "" (abstract (Symbol "" sid) a)) (foldl' (\a (_, phi) -> Impl phi a) (Atom a) decls') params'
        let es' = IntSet.foldl' (\es _ -> compileForallElims es) (foldl' (\es (_, phi) -> compileImplElims phi es) (compileAtomElims a) decls') params'
        s <- withSubgoal 1 (\_ -> insertElims p' phi' es')
        let p'' = foldr (\(s, _) p -> mkApp p (mkVar s)) (IntSet.foldr (\sid p -> mkAApp p (tfun (Symbol "" sid) [])) (mkVar s) params') decls'
        return (IntSet.singleton (sid s), DList.empty, 1 + length decls', p'')
      else
        cont d
    else
      cont d
  else
    cont d
  where
    cont d = do
      let elims = compileAtomElims a
      s <- withSubgoal d (\_ -> insertElims p (Atom a) elims)
      return (IntSet.singleton (sid s), DList.empty, 1, mkVar s)
    insertElims p phi elims = do
      s <- nextSymbol
      updateSpine (\sp p' -> sp (mkApp (mkLam s phi p') p))
      addElims s phi elims
      return s

{--------------------------------------------------------------------------------}
{- search -}

{- search limit (argument to search') should not be confused with context depth -}
{- search' limit visitedGoalAtoms env formula = (unbound symbols used, terms (evars), proof size, proof) -}
search' :: Proof p => Options -> Int -> [Atom] -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, Int, p)
search' _ 0 _ _ _ = failDepth
search' _ _ _ _ (PAtom (s, _)) | s == sBottom = empty
search' opts n visited env (PAtom a) = do
  bs <- lift $ mapM (atomEquals a') visited
  if or bs then
    empty
  else
    searchElim opts n visited a'
  where
    a' = subst env a
search' opts n visited env a@(PImpl (phi, _) a') = do
  b <- isInContext (subst env phi)
  if b then do
    s <- nextSymbol
    (su, ts, sz, p) <- search' opts n visited env a'
    return (su, ts, sz + 1, mkLam s phi p)
  else
    intros opts n env a
search' opts n _ env a@(PForall _ _) = intros opts n env a
search' opts n visited env (PAnd a b) = do
  (su1, ts1, sz1, p1) <- search' opts n visited env a
  (su2, ts2, sz2, p2) <- search' opts n visited env b
  return (IntSet.union su1 su2, DList.append ts1 ts2, sz1 + sz2 + 1, mkConj p1 p2)
search' opts n visited env (POr phi a b) = aux ILeft a <|> aux IRight b
  where
    aux idx c = do
      (su, ts, sz, p) <- search' opts n visited env c
      return (su, ts, sz + 1, mkInj idx (subst env phi) p)
search' opts n visited env (PExists _ phi a) = do
  v <- nextEVar
  (su, ts, sz, p) <- search' opts n visited (v:env) a
  return (su, DList.cons v ts, sz + 1, mkExIntro (subst env phi) v p)

intros :: Proof p => Options -> Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, Int, p)
intros opts n env a = do
  pushContext
  (su, ts, sz, p) <- intros' opts n env a
  ctx <- getContext
  mapM_ (resolveTermEVars n) ts
  sut <- checkParams ts
  popContext
  return (IntSet.difference
              (IntSet.difference (IntSet.union su sut)
                    (IntMap.keysSet (cDecls ctx)))
              (cParams ctx)
          , DList.empty, sz, p)

intros' :: Proof p => Options -> Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, Int, p)
intros' opts n env (PImpl (phi, elims) a) = do
  let phi' = subst env phi
  b <- addToContext phi'
  if b then do
    s <- nextSymbol
    let elims' = map (subst env) elims
    addElims s phi' elims'
    updateSpine (\sp p -> sp (mkLam s phi' p))
    intros' opts n env a
  else
    intros' opts n env a
intros' opts n env (PForall name a) = do
  s <- nextSymbolNamed name
  addParam s
  updateSpine (\sp p -> sp (mkALam s p))
  intros' opts n (tfun s [] : env) a
intros' opts n env x = do
  pushGoal (subst env x) -- this should remain lazy
  (su, ts, sz, p) <- searchAfterIntros opts n env x
  popGoal
  sp <- getSpine
  return (su, ts, sz, sp p)

searchElim :: Proof p => Options -> Int -> [Atom] -> Atom -> ProofMonad p (IntSet, DList Term, Int, p)
searchElim opts n visited a = do
  elims <- findElims a
  foldr (\(s,e) acc -> applyElim opts (n - 1) visited s e a <|> acc) empty elims

wrapExFalso :: Proof p => PFormula -> ProofMonad p (IntSet, DList Term, Int, p) -> ProofMonad p (IntSet, DList Term, Int, p)
wrapExFalso a m = do
  (su, ts, sz, p) <- m
  return (su, ts, sz, mkExfalso (decompileFormula a) p)

searchExFalso :: Proof p => Options -> Int -> PFormula -> ProofMonad p (IntSet, DList Term, Int, p)
searchExFalso opts n a = wrapExFalso a $ searchElim opts n [] aBottom

searchAfterIntros :: Proof p => Options -> Int -> [Term] -> PFormula ->
  ProofMonad p (IntSet, DList Term, Int, p)
searchAfterIntros _ 0 _ _ = failDepth
searchAfterIntros opts n _ (PAtom a) | a == aBottom = searchElim opts n [] aBottom
searchAfterIntros opts n env ga@(PAtom a) = do
  es1 <- findElims a
  es2 <- findElims aBottom
  foldr apElim empty (elims es1 es2)
  where
    elims es1 es2 = sortBy (\x y -> compare (cost (snd x)) (cost (snd y))) (es1 ++ es2)
    apElim (s, e) acc | fst (target e) == sBottom = wrapExFalso ga $ applyElim opts (n - 1) [] s e aBottom <|> acc
    apElim (s, e) acc = applyElim opts (n - 1) [] s e (subst env a) <|> acc
searchAfterIntros opts n env g = search' opts n [] env g <|> searchExFalso opts n (subst env g)

fixApplyElims :: Proof p => Options -> Int -> [Atom] -> [Term] -> Int -> Symbol -> [Elim PFormula]
  -> ProofMonad p ([Term], [Term], Int, p)
fixApplyElims opts n visited env k s es = do
  let (vars, env') = splitAt k env
  let env0 = reverse vars
  (su, ts, _, p) <- applyElims opts n visited env0 s es
  mapM_ (resolveTermEVars n) ts
  sut <- checkParams ts
  let su' = IntSet.union su sut
  d <- getMaxDepth su'
  return (env0, env', d, p)

applyElims :: Proof p => Options -> Int -> [Atom] -> [Term] -> Symbol -> [Elim PFormula] ->
  ProofMonad p (IntSet, DList Term, Int, p)
applyElims opts n visited env s es = do
  (sus, ts, sz, ps) <- foldr (search_subgoal . subst env) (return ([], DList.empty, 1, [])) es
  return (IntSet.insert (sid s) (IntSet.unions sus), ts, sz, mkElim s ps)
  where
    search_subgoal (EApp x) a = do
      (su, ts, sz1, p) <- search' opts n visited [] x
      (sus, ts', sz2, ps) <- a
      return (su : sus, DList.append ts ts', sz1 + sz2, EApp p : ps)
    search_subgoal (EAApp t) a = do
      (sus, ts, sz, ps) <- a
      return (sus, DList.cons t ts, sz + 1, EAApp t : ps)
    search_subgoal (EProj i) a = do
      (sus, ts, sz, ps) <- a
      return (sus, ts, sz, EProj i : ps)

applyCElims :: Proof p => Options -> Atom -> Int -> [Atom] -> [Term] -> [Symbol] -> Symbol -> CElims ->
  ProofMonad p (IntSet, DList Term, Int, p)
applyCElims opts a n visited env _ s (Elims _ es) = do
  (su, ts, sz, p) <- applyElims opts n visited (reverse env) s es
  if sz > optMemoizeThreshold opts then do
    vs <- lift $ U.getFreeVarsAll ts
    if null vs then
      ifte (memoizeProof opts a su ts p) return (return (su, ts, sz, p))
    else
      return (su, ts, sz, p)
  else
    return (su, ts, sz, p)
applyCElims opts a n visited env params s (ECase k es idx phi1 es1 phi2 es2 ces) = do
  (env0, env', d, p) <- fixApplyElims opts n visited env k s es
  s' <- withSubgoal d (solveCaseSubgoal env0 p)
  applyCElims opts a n visited env' params s' (subst env0 ces)
  where
    solveCaseSubgoal env0 p g = do
      checkCase s a
      (_, _, _, pg) <- search' opts n [] [] (PImpl (subst env0 phi2, map (subst env0) es2) g)
      s' <- nextSymbol
      let phi1' = subst env0 phi1
      updateSpine (\sp p' ->
        case idx of
          ILeft -> sp (mkCase p (mkLam s' phi1' p') pg)
          IRight -> sp (mkCase p pg (mkLam s' phi1' p')))
      addElims s' phi1' (map (subst env0) es1)
      return s'
applyCElims opts a n visited env params s (EEx _ k es phi eas ces) = do
  (env0, env', d, p) <- fixApplyElims opts n visited env k s es
  let sa = head params
  let env0' = tfun sa [] : env0
  let phi' = subst env0' phi
  s' <- withSubgoal d (insertExElim sa phi' p)
  addElims s' phi' (map (subst env0') eas)
  applyCElims opts a n visited (tail env') (tail params) s' (subst env0' ces)
  where
    insertExElim sa phi' p _ = do
      s' <- nextSymbol
      updateSpine (\sp p' ->
        sp (mkExElim p (mkALam sa (mkLam s' phi' p'))))
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
createEVars (EEx str k _ _ _ ces) = do
  env <- replicateM k nextEVar
  s <- nextSymbolNamed str
  (env', params) <- createEVars ces
  return (env ++ [tfun s []] ++ env', s : params)

applyElim :: Proof p => Options -> Int -> [Atom] -> Symbol -> Eliminator -> Atom ->
  ProofMonad p (IntSet, DList Term, Int, p)
applyElim opts n visited s e a =
  if optComplete opts then
    cont
  else do
    vs <- mapM (lift . U.getFreeVars) (snd a)
    if null vs then once cont else cont
  where
    cont = do
      (env, params) <- createEVars (elims e)
      let a' = second (map (subst (reverse env))) (target e)
      unifyAtoms a a'
      applyCElims opts a n (a:visited) env params s (elims e)

searchCompiled :: Proof p => Options -> ProofState p -> Int -> PFormula -> Either Bool [p]
searchCompiled opts ps n phi =
  observeE $
  evalIntBindingT $
  evalStateT
    (intros opts n [] phi >>= applyTermBindings')
    ps
  where
    applyTermBindings' (_, _, _, p) =
      applyTermBindings (\t -> resolveTermEVars n t >> U.applyBindings t) p

-- | `searchLimited sig depthLimit formula` returns:
-- * `Left True` when no proof was found and the search was interrupted due to
--   the depth limit
-- * `Left False` when no proof was found and the search was exhaustive
-- * `Right ps` when proofs `ps` were found
search :: Proof p => Options -> Signature -> Int -> Formula -> Either Bool [p]
search opts sig depthLimit formula =
  searchCompiled opts (initProofState sig) depthLimit (compileFormula formula)

-- | `searchIter` calls `search` in iterative deepening fashion
searchIter :: Proof p => Options -> Signature -> Formula -> [p]
searchIter opts sig formula = go 2
  where
    phi = compileFormula formula
    ps = initProofState sig
    go n =
      case searchCompiled opts ps n phi of
        Left True -> go (n + 1)
        Left False -> []
        Right ps -> ps
