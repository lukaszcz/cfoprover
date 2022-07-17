{-# LANGUAGE DeriveTraversable, DeriveGeneric, FlexibleInstances, FlexibleContexts  #-}

module Prover.Types where

import Control.Monad
import Control.Monad.Identity
import Control.Unification
import Control.Unification.IntVar
import Data.Hashable
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
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
data TermF t = Var !Int | Fun Symbol ![t] deriving (Eq, Functor, Foldable, Traversable)

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

extractSyms :: Term -> IntSet -> IntSet
extractSyms (UTerm (Fun s args)) su = foldl' (flip extractSyms) (IntSet.insert (sid s) su) args
extractSyms _ su = su

instance Eq Term where
  UVar v1 == UVar v2 = v1 == v2
  UTerm t1 == UTerm t2 = t1 == t2
  _ == _ = False

tvar :: Int -> Term
tvar x = UTerm $ Var x

tfun :: Symbol -> [Term] -> Term
tfun f args = UTerm $ Fun f args

data Atom = Atom !Symbol ![Term] deriving (Eq, Generic)

instance Hashable Atom where

atomArgs :: Atom -> [Term]
atomArgs (Atom _ args) = args

atomSym :: Atom -> Symbol
atomSym (Atom s _) = s

data Formula
  = Atomic !Atom
  | Impl !Formula !Formula
  | And !Formula !Formula
  | Or !Formula !Formula
  | Forall !String !Formula
  | Exists !String !Formula
  deriving (Generic)

-- this is not entirely correct because the quantifier variable names are not
-- ignored, but it works for the purposes of Search.hs
instance Hashable Formula where

mapAtoms' :: Applicative m => (Int -> [String] -> Atom -> m Atom) -> Int -> [String] -> Formula -> m Formula
mapAtoms' f n env (Atomic a) = Atomic <$> f n env a
mapAtoms' f n env (Impl x y) = Impl <$> mapAtoms' f n env x <*> mapAtoms' f n env y
mapAtoms' f n env (And x y) = And <$> mapAtoms' f n env x <*> mapAtoms' f n env y
mapAtoms' f n env (Or x y) = Or <$> mapAtoms' f n env x <*> mapAtoms' f n env y
mapAtoms' f n env (Forall s x) = Forall s <$> mapAtoms' f (n + 1) (s : env) x
mapAtoms' f n env (Exists s x) = Exists s <$> mapAtoms' f (n + 1) (s : env) x

mapAtomsM :: Applicative m => (Int -> [String] -> Atom -> m Atom) -> Formula -> m Formula
mapAtomsM f = mapAtoms' f 0 []

mapAtoms :: (Int -> [String] -> Atom -> Atom) -> Formula -> Formula
mapAtoms f a = runIdentity $ mapAtomsM (\n env x -> return (f n env x)) a

foldAtoms :: (Atom -> a -> a) -> a -> Formula -> a
foldAtoms f acc (Atomic a) = f a acc
foldAtoms f acc (Impl x y) = foldAtoms f (foldAtoms f acc y) x
foldAtoms f acc (And x y) = foldAtoms f (foldAtoms f acc y) x
foldAtoms f acc (Or x y) = foldAtoms f (foldAtoms f acc y) x
foldAtoms f acc (Forall _ x) = foldAtoms f acc x
foldAtoms f acc (Exists _ x) = foldAtoms f acc x

atomEquals :: BindingMonad TermF IntVar m => Atom -> Atom -> m Bool
atomEquals (Atom s1 args1) (Atom s2 args2) | s1 == s2 = and <$> zipWithM equals args1 args2
atomEquals _ _ = return False

mapTermsInFormula :: Monad m => (Term -> m Term) -> Formula -> m Formula
mapTermsInFormula f = mapAtomsM (\_ _ (Atom s args) -> mapM f args >>= \args' -> pure $! Atom s args')

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
    go sig (Atomic (Atom s args)) = goTerm True sig (UTerm (Fun s args))
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
aBottom = Atom sBottom []

fBottom :: Formula
fBottom = Atomic aBottom

sTop :: Symbol
sTop = Symbol "⊤" 1

aTop :: Atom
aTop = Atom sTop []

fTop :: Formula
fTop = Atomic aTop

sEquality :: Symbol
sEquality = Symbol "=" 2

aEqual :: Term -> Term -> Atom
aEqual t1 t2 = Atom sEquality [t1, t2]

fEqual :: Term -> Term -> Formula
fEqual t1 t2 = Atomic (aEqual t1 t2)

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
  nsubst n env (Atom s args) = Atom s (map (nsubst n env) args)

instance Abstractable Atom where
  nabstract n s (Atom s' args) = Atom s' (map (nabstract n s) args)

instance Substitutable Formula where
  nsubst n env = mapAtoms (\m _ -> nsubst (n + m) env)

instance Abstractable Formula where
  nabstract n s = mapAtoms (\m _ -> nabstract (n + m) s)

instance Eq Formula where
  (Atomic (Atom s1 args1)) == (Atomic (Atom s2 args2)) = s1 == s2 && args1 == args2
  (Impl a1 b1) == (Impl a2 b2) = a1 == a2 && b1 == b2
  (And a1 b1) == (And a2 b2) = a1 == a2 && b1 == b2
  (Or a1 b1) == (Or a2 b2) = a1 == a2 && b1 == b2
  (Forall _ a1) == (Forall _ a2) = a1 == a2
  (Exists _ a1) == (Exists _ a2) = a1 == a2
  _ == _ = False

{-------------------------------------------------------------------}
{- show & read formulas -}

instance Show Symbol where
  showsPrec _ s =
    case sname s of
      "" -> showString "X" . shows (sid s)
      name -> showString name

showsTerm :: Term -> ShowS
showsTerm (UVar v) = showString "?" . shows (getVarID v)
showsTerm (UTerm (Var x)) = showString "_?v" . shows x
showsTerm (UTerm (Fun s args)) = shows s . sargs
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

instance Show Atom where
  show (Atom s args) = showTerm (UTerm (Fun s args))

instance Show Formula where
  showsPrec = showsFormula []
    where
      showsFormula :: [String] -> Int -> Formula -> ShowS
      showsFormula env p (Atomic (Atom s args)) = showParen (p > atom_prec) $
        showsTerm (UTerm (Fun s (map (subst (map (\x -> tfun (Symbol x 0) []) env)) args)))
        where
          atom_prec = 7
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
          forall_prec = 8
      showsFormula env p (Exists s a) =
        showParen (p > exists_prec) $
          showString "∃" . showString s . showsFormula (s : env) exists_prec a
        where
          exists_prec = 8
