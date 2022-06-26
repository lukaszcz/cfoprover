{-# LANGUAGE DeriveTraversable, DeriveGeneric, FlexibleInstances, FlexibleContexts, UnicodeSyntax #-}

module Formula where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Identity
import Control.Unification
import Control.Unification.IntVar
import Data.Hashable
import Data.Bifunctor
import Data.Char
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.List as List
import Data.List.Extras.Pair
import GHC.Generics

{------------------------------------}
{- terms & formulas -}

data Symbol = Symbol {sname :: String, sid :: Int}

instance Eq Symbol where
  s1 == s2 = sid s1 == sid s2

instance Hashable Symbol where
  hashWithSalt k s = hashWithSalt k (sid s)

-- terms and formulas use 0-based de-Bruijn indices
data TermF t = Var Int | Fun Symbol [t] deriving (Eq, Functor, Foldable, Traversable)

instance Unifiable TermF where
  zipMatch (Var x) (Var y)
    | x == y = Just $ Var x
  zipMatch (Fun f1 args1) (Fun f2 args2)
    | f1 == f2 = fmap (Fun f1) (pairWith (curry Right) args1 args2)
  zipMatch _ _ = Nothing

type Term = UTerm TermF IntVar

instance Hashable Term where
  hashWithSalt k (UVar v) = hashWithSalt k (0 :: Int, getVarID v)
  hashWithSalt k (UTerm (Var v)) = hashWithSalt k (1 :: Int, v)
  hashWithSalt k (UTerm (Fun s args)) = hashWithSalt k (2 :: Int, (sid s, args))

varOccurs :: Int -> Term -> Bool
varOccurs n (UTerm (Var m)) = n == m
varOccurs n (UTerm (Fun _ args)) = any (varOccurs n) args
varOccurs _ _ = False

instance Eq Term where
  UVar v1 == UVar v2 = v1 == v2
  UTerm t1 == UTerm t2 = t1 == t2
  _ == _ = False

tvar :: Int -> Term
tvar x = UTerm $ Var x

tfun :: Symbol -> [Term] -> Term
tfun f args = UTerm $ Fun f args

type Atom = (Symbol, [Term])

data Formula
  = Atom Atom
  | Impl Formula Formula
  | And Formula Formula
  | Or Formula Formula
  | Forall String Formula
  | Exists String Formula
  deriving (Generic)

-- this is not entirely correct because the quantifier variable names are not
-- ignored, but it works for the purposes of Search.hs
instance Hashable Formula where

mapAtoms' :: Applicative m => (Int -> [String] -> Atom -> m Atom) -> Int -> [String] -> Formula -> m Formula
mapAtoms' f n env (Atom a) = Atom <$> f n env a
mapAtoms' f n env (Impl x y) = Impl <$> mapAtoms' f n env x <*> mapAtoms' f n env y
mapAtoms' f n env (And x y) = And <$> mapAtoms' f n env x <*> mapAtoms' f n env y
mapAtoms' f n env (Or x y) = Or <$> mapAtoms' f n env x <*> mapAtoms' f n env y
mapAtoms' f n env (Forall s x) = Forall s <$> mapAtoms' f (n + 1) (s : env) x
mapAtoms' f n env (Exists s x) = Exists s <$> mapAtoms' f (n + 1) (s : env) x

mapAtomsM :: Applicative m => (Int -> [String] -> Atom -> m Atom) -> Formula -> m Formula
mapAtomsM f = mapAtoms' f 0 []

mapAtoms :: (Int -> [String] -> Atom -> Atom) -> Formula -> Formula
mapAtoms f a = runIdentity $ mapAtomsM (\n env x -> return (f n env x)) a

atomEquals :: BindingMonad TermF IntVar m => Atom -> Atom -> m Bool
atomEquals (s1, args1) (s2, args2) | s1 == s2 = and <$> zipWithM equals args1 args2
atomEquals _ _ = return False

data Signature = Signature
  { functionSymbols :: [Symbol],
    predicateSymbols :: [Symbol],
    symbolArity :: IntMap Int,
    maxSymbolId :: Int
  }

createSignature :: Formula -> Signature
createSignature phi =
  sig
    { functionSymbols = sortUnique (functionSymbols sig)
    , predicateSymbols = sortUnique (predicateSymbols sig) }
  where
    sig = go (Signature [] [] IntMap.empty 0) phi
    go sig (Atom (s, args)) = goTerm True sig (UTerm (Fun s args))
    go sig (Impl a b) = go (go sig a) b
    go sig (And a b) = go (go sig a) b
    go sig (Or a b) = go (go sig a) b
    go sig (Forall _ a) = go sig a
    go sig (Exists _ a) = go sig a
    goTerm isPred sig (UTerm (Fun s args)) =
      foldl' (goTerm False) sig' args
      where
        sig0 =
            sig
              { symbolArity = IntMap.insert (sid s) (length args) (symbolArity sig),
                maxSymbolId = max (maxSymbolId sig) (sid s)
              }
        sig' =
          if isPred then
            sig0{ predicateSymbols = s : predicateSymbols sig }
          else
            sig0{ functionSymbols = s : functionSymbols sig }
    goTerm _ sig _ = sig
    unique (x : y : t) | x == y = unique (x : t)
    unique (x : t) = x : unique t
    unique [] = []
    sortUnique = unique . sortBy (\x y -> compare (sid x) (sid y))

{----------------------------------------------------------------------------}
{- standard symbols & formulas -}

sBottom :: Symbol
sBottom = Symbol "⊥" 0

aBottom :: Atom
aBottom = (sBottom, [])

fBottom :: Formula
fBottom = Atom aBottom

sTop :: Symbol
sTop = Symbol "⊤" 1

aTop :: Atom
aTop = (sTop, [])

fTop :: Formula
fTop = Atom aTop

sEquality :: Symbol
sEquality = Symbol "=" 2

aEqual :: Term -> Term -> Atom
aEqual t1 t2 = (sEquality, [t1, t2])

fEqual :: Term -> Term -> Formula
fEqual t1 t2 = Atom (aEqual t1 t2)

tMinSymbol :: Int
tMinSymbol = 3

{------------------------------------------------------------------}
{- substitution -}

class Substitutable a where
  -- nsubst n env t -> substitute variable with index (x + n) by (env !! x)
  nsubst :: Int -> [Term] -> a -> a

subst :: Substitutable a => [Term] -> a -> a
subst [] x = x
subst env x = nsubst 0 env x

shift :: Substitutable t => Int -> t -> t
shift 0 = id
shift k = subst (map (\n -> tvar (n + k)) [0, 1 ..])

class Abstractable a where
  -- nabstract n f t -> change function f into variable n
  nabstract :: Int -> Symbol -> a -> a

abstract :: Abstractable a => Symbol -> a -> a
abstract = nabstract 0

instance Substitutable Term where
  nsubst n env (UTerm (Var x)) | x >= n = env !! (x - n)
  nsubst n env (UTerm (Fun f args)) = UTerm $ Fun f (map (nsubst n env) args)
  nsubst _ _ t = t

instance Abstractable Term where
  nabstract n s (UTerm (Fun f [])) | f == s = UTerm (Var n)
  nabstract n s (UTerm (Fun f args)) = UTerm (Fun f (map (nabstract n s) args))
  nabstract _ _ t = t

instance Substitutable Atom where
  nsubst n env (s, args) = (s, map (nsubst n env) args)

instance Abstractable Atom where
  nabstract n s (s', args) = (s', map (nabstract n s) args)

instance Substitutable Formula where
  nsubst n env = mapAtoms (\m _ -> nsubst (n + m) env)

instance Abstractable Formula where
  nabstract n s = mapAtoms (\m _ -> nabstract (n + m) s)

instance Eq Formula where
  (Atom (s1, args1)) == (Atom (s2, args2)) = s1 == s2 && args1 == args2
  (Impl a1 b1) == (Impl a2 b2) = a1 == a2 && b1 == b2
  (And a1 b1) == (And a2 b2) = a1 == a2 && b1 == b2
  (Or a1 b1) == (Or a2 b2) = a1 == a2 && b1 == b2
  (Forall _ a1) == (Forall _ a2) = a1 == a2
  (Exists _ a1) == (Exists _ a2) = a1 == a2
  _ == _ = False

{-------------------------------------------------------------------}
{- show & read formulas -}

showsSymbol :: Symbol -> ShowS
showsSymbol s =
  case sname s of
    "" -> showString "X" . shows (sid s)
    name -> showString name

showsTerm :: Term -> ShowS
showsTerm (UVar v) = showString "?" . shows (getVarID v)
showsTerm (UTerm (Var x)) = showString "_?v" . shows x
showsTerm (UTerm (Fun s args)) = showsSymbol s . sargs
  where
    sargs =
      if null args
        then id
        else
          showChar '('
            . foldl (\a x -> a . showString "," . showsTerm x) (showsTerm (head args)) (tail args)
            . showChar ')'

showTerm :: Term -> String
showTerm t = showsTerm t ""

showAtom :: (Symbol, [Term]) -> String
showAtom (s, args) = showTerm (UTerm (Fun s args))

showsFormula :: [String] -> Int -> Formula -> ShowS
showsFormula env _ (Atom (s, args)) =
  showsTerm (UTerm (Fun s (map (subst (map (\x -> tfun (Symbol x 0) []) env)) args)))
showsFormula env p (Impl a b) =
  showParen (p > impl_prec) $
    showsFormula env (impl_prec + 1) a . showString " → "
      . showsFormula env impl_prec b
  where
    impl_prec = 5
showsFormula env p (And a b) =
  showParen (p > and_prec) $
    showsFormula env (and_prec + 1) a . showString " ∧ "
      . showsFormula env (and_prec + 1) b
  where
    and_prec = 6
showsFormula env p (Or a b) =
  showParen (p > or_prec) $
    showsFormula env (or_prec + 1) a . showString " ∨ "
      . showsFormula env (or_prec + 1) b
  where
    or_prec = 6
showsFormula env p (Forall s a) =
  showParen (p > forall_prec) $
    showString "∀" . showString s . showsFormula (s : env) forall_prec a
  where
    forall_prec = 7
showsFormula env p (Exists s a) =
  showParen (p > exists_prec) $
    showString "∃" . showString s . showsFormula (s : env) exists_prec a
  where
    exists_prec = 7

instance Show Formula where
  showsPrec = showsFormula []

-- (line, char)
type Position = (Int, Int)

data ReadState = ReadState {rSyms :: HashMap String Int, rSymId :: Int}
data ReadError = ReadError {rPosition :: Position, rMessage :: String}

-- (position, remaining input)
type Input = (Position, String)
type ReadMonad a = ExceptT ReadError (State ReadState) a

readError :: String -> Input -> ReadMonad a
readError msg i = throwError $ ReadError (fst i) msg

newSymbol :: String -> ReadMonad Symbol
newSymbol s = do
  rs <- get
  let id = rSymId rs
  put rs {rSyms = HashMap.insert s id (rSyms rs), rSymId = id + 1}
  return $ Symbol s id

getSymbol :: String -> ReadMonad Symbol
getSymbol s = do
  rs <- get
  case HashMap.lookup s (rSyms rs) of
    Just id -> return $ Symbol s id
    Nothing -> newSymbol s

skipWhitespace :: Input -> Input
skipWhitespace ((l, _), '\n' : s) = skipWhitespace ((l+1, 0), s)
skipWhitespace ((l, n), c : s) | isSpace c = skipWhitespace ((l, n+1), s)
skipWhitespace i = i

readLexeme :: Input -> Maybe (String, Input)
readLexeme s =
  let ((l,n),s1) = skipWhitespace s in
  case s1 of
    '&' : s' -> Just ("and", ((l,n+1),s'))
    '|' : s' -> Just ("or", ((l,n+1),s'))
    '/' : '\\' : s' -> Just ("and", ((l,n+2),s'))
    '\\' : '/' : s' -> Just ("or", ((l,n+2),s'))
    '-' : '>' : s' -> Just ("->", ((l,n+2),s'))
    '<' : '-' : '>' : s' -> Just ("<->", ((l,n+3),s'))
    '~' : s' -> Just ("not", ((l,n+1),s'))
    '⊥' : s' -> Just ("false", ((l,n+1),s'))
    '⊤' : s' -> Just ("true", ((l,n+1),s'))
    '∧' : s' -> Just ("and", ((l,n+1),s'))
    '∨' : s' -> Just ("or", ((l,n+1),s'))
    '→' : s' -> Just ("->", ((l,n+1),s'))
    '∀' : s' -> Just ("forall", ((l,n+1),s'))
    '∃' : s' -> Just ("exists", ((l,n+1),s'))
    s'@(c : _) | isAlpha c -> Just $ readIdent ((l,n),s')
    c : s' -> Just ([c], ((l,n+1),s'))
    _ -> Nothing
  where
    readIdent ((l,n),c:s)
      | isAlphaNum c || c == '_' || c == '-' || c == '\'' =
        let (s1, out) = readIdent ((l,n+1),s)
         in (c : s1, out)
    readIdent s = ("", s)

readTerm :: Input -> ReadMonad (Term, Input)
readTerm s =
  case readLexeme s of
    Just (sf, s') -> do
      sym <- getSymbol sf
      (args, s'') <- readArgs readTerm s'
      return (UTerm (Fun sym args), s'')
    _ -> readError "expected a term" s

readArgs :: (Input -> ReadMonad (a, Input)) -> Input -> ReadMonad ([a], Input)
readArgs f s =
  case readLexeme s of
    Just ("(", s1) -> go s1
    _ -> return ([], s)
  where
    go s0 = do
      (t, s1) <- f s0
      case readLexeme s1 of
        Just (",", s2) -> do
          (ts, s3) <- go s2
          return (t : ts, s3)
        Just (")", s2) -> return ([t], s2)
        _ -> readError "expected ')'" s0

readAtom :: Input -> ReadMonad (Formula, Input)
readAtom s =
  case readLexeme s of
    Just ("(", s') -> do
      (r, s'') <- readFormula' s'
      case readLexeme s'' of
        Just (")", s3) -> return (r, s3)
        _ -> readError "expected ')'" s''
    Just ("true", s') -> return (fTop, s')
    Just ("false", s') -> return (fBottom, s')
    Just (sf, s') -> do
      sym <- getSymbol sf
      (args, s'') <- readArgs readTerm s'
      return (Atom (sym, args), s'')
    _ -> readError "expected an atom" s

readNegQuant :: Input -> ReadMonad (Formula, Input)
readNegQuant s =
  case readLexeme s of
    Just ("not", s1) -> do
      (r, s2) <- readNegQuant s1
      return (Impl r fBottom, s2)
    Just ("forall", s1) -> go Forall s1
    Just ("exists", s1) -> go Exists s1
    _ -> readAtom s
  where
    go q s1 =
      case readLexeme s1 of
        Just (x, s2) -> do
          sym <- newSymbol x
          case readLexeme s2 of
            Just (".", s3) -> do
              (r, s4) <- readFormula' s3
              return (q x (abstract sym r), s4)
            _ -> do
              (r, s3) <- readNegQuant s2
              return (q x (abstract sym r), s3)
        _ -> readError "expected variable name" s1

readConjunction :: Input -> ReadMonad (Formula, Input)
readConjunction s = do
  (a1, s1) <- readNegQuant s
  case readLexeme s1 of
    Just ("and", s2) -> do
      (a2, s3) <- readConjunction s2
      return (And a1 a2, s3)
    _ -> return (a1, s1)

readDisjunction :: Input -> ReadMonad (Formula, Input)
readDisjunction s = do
  (a1, s1) <- readConjunction s
  case readLexeme s1 of
    Just ("or", s2) -> do
      (a2, s3) <- readDisjunction s2
      return (Or a1 a2, s3)
    _ -> return (a1, s1)

readImplication :: Input -> ReadMonad (Formula, Input)
readImplication s = do
  (a1, s1) <- readDisjunction s
  case readLexeme s1 of
    Just ("->", s2) -> do
      (a2, s3) <- readImplication s2
      return (Impl a1 a2, s3)
    _ -> return (a1, s1)

readEquivalence :: Input -> ReadMonad (Formula, Input)
readEquivalence s = do
  (a1, s1) <- readImplication s
  case readLexeme s1 of
    Just ("<->", s2) -> do
      (a2, s3) <- readEquivalence s2
      return (And (Impl a1 a2) (Impl a2 a1), s3)
    _ -> return (a1, s1)

readFormula' :: Input -> ReadMonad (Formula, Input)
readFormula' = readEquivalence

readFormula'' :: String -> Either ReadError (Formula, Input)
readFormula'' s =
  evalState (runExceptT $ readFormula' ((1,1),s)) (ReadState HashMap.empty tMinSymbol)

readFormula :: String -> Either ReadError Formula
readFormula s = case readFormula'' s of
                  Left e -> Left e
                  Right (_, (p, s)) | s /= "" -> Left $ ReadError p "input remaining"
                  Right (phi, _) -> Right phi

instance Read Formula where
  readsPrec _ s = case readFormula'' s of
                    Left e -> error $ show (rPosition e) ++ ": " ++ rMessage e
                    Right x -> [second snd x]

{-------------------------------------------------------------------}
{- proof terms -}

data Idx = ILeft | IRight

data Elim p = EApp p | EAApp Term | EProj Idx

instance Substitutable a => Substitutable (Elim a) where
  nsubst n env (EApp x) = EApp (nsubst n env x)
  nsubst n env (EAApp t) = EAApp (nsubst n env t)
  nsubst _ _ e@(EProj _) = e

class Show p => Proof p where
  mkVar :: Symbol -> p
  mkLam :: Symbol -> Formula -> p -> p
  mkApp :: p -> p -> p
  mkConj :: p -> p -> p
  mkProj :: Idx -> p -> p
  mkInj :: Idx -> Formula -> p -> p
  mkCase :: p -> p -> p -> p
  mkALam :: Symbol -> p -> p
  mkAApp :: p -> Term -> p
  mkExIntro :: Formula -> Term -> p -> p
  mkExElim :: p -> p -> p
  mkExfalso :: Formula -> p -> p
  mkElim :: Symbol -> [Elim p] -> p
  mkElim s elims = mk (mkVar s) elims
    where
      mk p [] = p
      mk p (EApp p' : es) = mk (mkApp p p') es
      mk p (EAApp t : es) = mk (mkAApp p t) es
      mk p (EProj i : es) = mk (mkProj i p) es
  applyTermBindings :: Monad m => (Term -> m Term) -> p -> m p

instance Proof () where
  mkVar _ = ()
  mkLam _ _ _ = ()
  mkApp _ _ = ()
  mkConj _ _ = ()
  mkProj _ _ = ()
  mkInj _ _ _ = ()
  mkCase _ _ _ = ()
  mkALam _ _ = ()
  mkAApp _ _ = ()
  mkExIntro _ _ _ = ()
  mkExElim _ _ = ()
  mkExfalso _ _ = ()
  mkElim _ _ = ()
  applyTermBindings _ _ = return ()

data PTerm
  = PVar Symbol
  | Lambda Symbol Formula PTerm
  | App PTerm PTerm
  | Conj PTerm PTerm
  | Proj Idx PTerm
  | Inj Idx Formula PTerm -- Inj ILeft a t :: a
  | Case PTerm PTerm PTerm
  | ALambda Symbol PTerm
  | AApp PTerm Term
  | ExIntro Formula Term PTerm -- ExIntro a tt t :: a
  | ExElim PTerm PTerm
  | Exfalso Formula PTerm

mapTerms :: Monad m => (Term -> m Term) -> PTerm -> m PTerm
mapTerms _ x@(PVar _) = pure x
mapTerms f (Lambda s phi x) = (Lambda s <$> mapAtomsM (\_ _ (s,args) -> mapM f args >>= \args' -> pure (s, args')) phi) <*> mapTerms f x
mapTerms f (App x y) = App <$> mapTerms f x <*> mapTerms f y
mapTerms f (Conj x y) = Conj <$> mapTerms f x <*> mapTerms f y
mapTerms f (Proj idx x) = Proj idx <$> mapTerms f x
mapTerms f (Inj idx phi x) = Inj idx phi <$> mapTerms f x
mapTerms f (Case x y z) = Case <$> mapTerms f x <*> mapTerms f y <*> mapTerms f z
mapTerms f (ALambda s x) = ALambda s <$> mapTerms f x
mapTerms f (AApp x t) = AApp <$> mapTerms f x <*> f t
mapTerms f (ExIntro phi t x) = ExIntro phi <$> f t <*> mapTerms f x
mapTerms f (ExElim x y) = ExElim <$> mapTerms f x <*> mapTerms f y
mapTerms f (Exfalso phi x) = Exfalso phi <$> mapTerms f x

instance Proof PTerm where
  mkVar = PVar
  mkLam = Lambda
  mkApp = App
  mkConj = Conj
  mkProj = Proj
  mkInj = Inj
  mkCase = Case
  mkALam = ALambda
  mkAApp = AApp
  mkExIntro = ExIntro
  mkExElim = ExElim
  mkExfalso = Exfalso
  applyTermBindings = mapTerms

instance Show PTerm where
  showsPrec _ (PVar s) = showsSymbol s
  showsPrec d (Lambda s phi p) =
    showParen (d > lambda_prec) $
      showString "λ" . showsSymbol s . showString " : " . shows phi
        . showString " . "
        . showsPrec lambda_prec p
    where
      lambda_prec = 0
  showsPrec d (App p1 p2) =
    showParen (d > app_prec) $
      showsPrec app_prec p1 . showString " " . showsPrec (app_prec + 1) p2
    where
      app_prec = 5
  showsPrec _ (Conj p1 p2) =
    showString "(" . showsPrec app_prec p1 . showString ", "
      . showsPrec app_prec p2
      . showString ")"
    where
      app_prec = 5
  showsPrec d (Proj idx p) =
    showParen (d > app_prec) $
      showString (case idx of ILeft -> "π1 "; IRight -> "π2 ")
        . showsPrec (app_prec + 1) p
    where
      app_prec = 5
  showsPrec d (Inj idx _ p) =
    showParen (d > app_prec) $
      showString (case idx of ILeft -> "in1 "; IRight -> "in2 ")
        . showsPrec (app_prec + 1) p
    where
      app_prec = 5
  showsPrec d (Case p p1 p2) =
    showParen (d > lambda_prec) $
      showString "case " . showsPrec (app_prec + 1) p . showString " { "
        . showsPrec lambda_prec p1
        . showString " | "
        . showsPrec lambda_prec p2
        . showString " }"
    where
      app_prec = 5
      lambda_prec = 0
  showsPrec d (ALambda s p) =
    showParen (d > lambda_prec) $
      showString "Λ" . showsSymbol s
        . showString " . "
        . showsPrec lambda_prec p
    where
      lambda_prec = 0
  showsPrec d (AApp p t) =
    showParen (d > app_prec) $
      showsPrec app_prec p . showString " " . showsTerm t
    where
      app_prec = 5
  showsPrec _ (ExIntro _ t p) =
    showString "[" . showsTerm t . showString ", "
      . showsPrec lambda_prec p
      . showString "]"
    where
      lambda_prec = 0
  showsPrec d (ExElim p1 p2) =
    showParen (d > lambda_prec) $
      showString "let " . showsPrec app_prec p1 . showString " be "
        . showsPrec lambda_prec p2
    where
      app_prec = 5
      lambda_prec = 0
  showsPrec d (Exfalso _ p) =
    showParen (d > app_prec) $
      showString "exfalso " . showsPrec (app_prec + 1) p
    where
      app_prec = 5

{------------------------------------}
{- proof checking -}

infer' :: [(Symbol, Formula)] -> PTerm -> Maybe Formula
infer' env (PVar s) = List.lookup s env
infer' env (Lambda s a t) = do
  b <- infer' ((s, a) : env) t
  return $ Impl a b
infer' env (App t1 t2) = do
  a <- infer' env t1
  case a of
    Impl a1 a2 -> do
      b <- infer' env t2
      guard $ b == a1
      return a2
    _ -> Nothing
infer' env (Conj t1 t2) = do
  a <- infer' env t1
  b <- infer' env t2
  return (And a b)
infer' env (Proj i t) = do
  a <- infer' env t
  case a of
    And a1 a2 -> case i of
      ILeft -> return a1
      IRight -> return a2
    _ -> Nothing
infer' env (Inj i a t) = do
  b <- infer' env t
  case i of
    ILeft -> return (Or b a)
    IRight -> return (Or a b)
infer' env (Case t0 t1 t2) = do
  a <- infer' env t0
  case a of
    Or a1 a2 -> do
      b1 <- infer' env t1
      b2 <- infer' env t2
      case (b1, b2) of
        (Impl a1' b1', Impl a2' b2')
          | a1 == a1' && a2 == a2' && b1' == b2' -> return b1'
        _ -> Nothing
    _ -> Nothing
infer' env (ALambda s t) = do
  a <- infer' env t
  return (Forall (sname s) (abstract s a))
infer' env (AApp t tt) = do
  a <- infer' env t
  case a of
    Forall _ a' -> return $ subst [tt] a'
    _ -> Nothing
infer' env (ExIntro a0@(Exists _ a) tt t) = do
  a' <- infer' env t
  guard $ subst [tt] a == a'
  return a0
infer' _ ExIntro {} = Nothing
infer' env (ExElim t t') = do
  a <- infer' env t
  case a of
    Exists _ a' -> do
      b <- infer' env t'
      case b of
        Forall _ (Impl b1 b2) | b1 == a' -> return b2
        _ -> Nothing
    _ -> Nothing
infer' env (Exfalso phi t) = do
  a <- infer' env t
  if a == fBottom then Just phi else Nothing

infer :: PTerm -> Maybe Formula
infer = infer' []

check :: PTerm -> Formula -> Bool
check t a = case infer t of
  Nothing -> False
  Just a' -> a == a'
