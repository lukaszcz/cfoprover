{-# LANGUAGE DeriveTraversable, FlexibleInstances #-}
module Formula where

import Data.Functor
import Data.List as List
import Data.List.Extras.Pair

import Control.Monad
import Control.Unification
import Control.Unification.IntVar

{------------------------------------}
{- Terms, formulas, proof terms -}

data Symbol = Symbol { sname :: String, sid :: Int }

instance Eq Symbol where
    s1 == s2 = sid s1 == sid s2

-- terms and formulas use 0-based de-Bruijn indices
data TermF t = Var Int | Fun Symbol [t] deriving (Eq, Functor, Foldable, Traversable)

instance Unifiable TermF where
    zipMatch (Var x) (Var y)
        | x == y = Just $ Var x
    zipMatch (Fun f1 args1) (Fun f2 args2)
        | f1 == f2 = fmap (Fun f1) (pairWith (curry Right) args1 args2)
    zipMatch _ _ = Nothing

type Term = UTerm TermF IntVar

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

sBottom :: Symbol
sBottom = Symbol "False" 0

aBottom :: Atom
aBottom = (sBottom, [])

fBottom :: Formula
fBottom = Atom aBottom

sTop :: Symbol
sTop = Symbol "True" 1

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

data Formula = Atom Atom
            | Impl Formula Formula
            | And Formula Formula
            | Or Formula Formula
            | Forall String Formula
            | Exists String Formula

mapAtoms' :: (Int -> [String] -> Atom -> Atom) -> Int -> [String] -> Formula -> Formula
mapAtoms' f n env (Atom a) = Atom (f n env a)
mapAtoms' f n env (Impl x y) = Impl (mapAtoms' f n env x) (mapAtoms' f n env y)
mapAtoms' f n env (And x y) = And (mapAtoms' f n env x) (mapAtoms' f n env y)
mapAtoms' f n env (Or x y) = Or (mapAtoms' f n env x) (mapAtoms' f n env y)
mapAtoms' f n env (Forall s x) = Forall s (mapAtoms' f (n + 1) (s:env) x)
mapAtoms' f n env (Exists s x) = Exists s (mapAtoms' f (n + 1) (s:env) x)

mapAtoms :: (Int -> [String] -> Atom -> Atom) -> Formula -> Formula
mapAtoms f = mapAtoms' f 0 []

data Idx = ILeft | IRight

data Elim p = EApp p | EAApp Term | EProj Idx

class Substitutable a where
    -- nsubst n env t -> substitute variable with index (x + n) by (env !! x)
    nsubst :: Int -> [Term] -> a -> a

subst :: Substitutable a => [Term] -> a -> a
subst [] x = x
subst env x = nsubst 0 env x

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

instance Substitutable a => Substitutable (Elim a) where
    nsubst n env (EApp x) = EApp (nsubst n env x)
    nsubst n env (EAApp t) = EAApp (nsubst n env t)
    nsubst _ _ e@(EProj _) = e

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

class Proof p where
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
    mkElim _ _ = ()
    applyTermBindings _ _ = return ()

data PTerm = PVar Symbol
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

mapTerms :: Monad m => (Term -> m Term) -> PTerm -> m PTerm
mapTerms _ x@(PVar _) = return x
mapTerms f (Lambda s phi x) = mapTerms f x <&> Lambda s phi
mapTerms f (App x y) = do
    x' <- mapTerms f x
    y' <- mapTerms f y
    return $ App x' y'
mapTerms f (Conj x y) = do
    x' <- mapTerms f x
    y' <- mapTerms f y
    return $ Conj x' y'
mapTerms f (Proj idx x) = mapTerms f x <&> Proj idx
mapTerms f (Inj idx phi x) = mapTerms f x <&> Inj idx phi
mapTerms f (Case x y z) =  do
    x' <- mapTerms f x
    y' <- mapTerms f y
    z' <- mapTerms f z
    return $ Case x' y' z'
mapTerms f (ALambda s x) = mapTerms f x <&> ALambda s
mapTerms f (AApp x t) = do
    x' <- mapTerms f x
    t' <- f t
    return $ AApp x' t'
mapTerms f (ExIntro phi t x) =  do
    x' <- mapTerms f x
    t' <- f t
    return $ ExIntro phi t' x'
mapTerms f (ExElim x y) =  do
    x' <- mapTerms f x
    y' <- mapTerms f y
    return $ ExElim x' y'

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
    applyTermBindings = mapTerms

{------------------------------------}
{- Proof checking -}

infer' :: [(Symbol, Formula)] -> PTerm -> Maybe Formula
infer' env (PVar s) = List.lookup s env
infer' env (Lambda s a t) = do
    b <- infer' ((s,a):env) t
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

infer :: PTerm -> Maybe Formula
infer = infer' []

check :: PTerm -> Formula -> Bool
check t a = case infer t of
  Nothing -> False
  Just a' -> a == a'

{------------------------------------}
{- Optimized formula representation -}

data CElims =
      Elims Int [Elim PFormula]
    | ECase Int [Elim PFormula] Idx Formula [Eliminator] Formula [Eliminator] CElims
    | EEx Int [Elim PFormula] Formula [Eliminator] CElims

data Eliminator = Eliminator {
      target :: Atom
    , elims :: CElims
    , bindersNum :: Int
    , cost :: Int
    }

data PFormula = PAtom Atom
              | PImpl (Formula, [Eliminator]) PFormula
              | PAnd PFormula PFormula
              | POr Formula PFormula PFormula
              | PForall String PFormula
              | PExists String Formula PFormula

instance Substitutable CElims where
    nsubst n env (Elims k es) = Elims k (map (nsubst n env) es)
    nsubst n env (ECase k es i a eas b ebs cs) =
        ECase k (map (nsubst n env) es) i
            (nsubst (n + k) env a) (map (nsubst (n + k) env) eas)
            (nsubst (n + k) env b) (map (nsubst (n + k) env) ebs)
            (nsubst (n + k) env cs)
    nsubst n env (EEx k es a eas cs) =
        EEx k (map (nsubst n env) es)
            (nsubst (n + k + 1) env a)
            (map (nsubst (n + k + 1) env) eas)
            (nsubst (n + k + 1) env cs)

instance Substitutable Eliminator where
    nsubst n env e = e{ target = nsubst n env (target e)
                      , elims = nsubst n env (elims e) }

instance Substitutable PFormula where
    nsubst n env (PAtom a) = PAtom $ nsubst n env a
    nsubst n env (PImpl (phi, elims) a) =
        PImpl (nsubst n env phi, map (nsubst n env) elims) (nsubst n env a)
    nsubst n env (PAnd a b) = PAnd (nsubst n env a) (nsubst n env b)
    nsubst n env (POr phi a b) = POr (nsubst n env phi) (nsubst n env a) (nsubst n env b)
    nsubst n env (PForall s a) = PForall s (nsubst (n + 1) env a)
    nsubst n env (PExists s phi a) = PExists s (nsubst n env phi) (nsubst (n + 1) env a)

shift :: Substitutable t => Int -> t -> t
shift 0 = id
shift k = subst (map (\n -> tvar (n + k)) [0,1..])

prependElim :: Elim PFormula -> CElims -> CElims
prependElim e (Elims k es) = Elims k (shift k e : es)
prependElim e (ECase k es idx a1 es1 a2 es2 elims) = ECase k (shift k e : es) idx a1 es1 a2 es2 elims
prependElim e (EEx k es a eas elims) = EEx k (shift k e : es) a eas elims

prependForallElim :: CElims -> CElims
prependForallElim (Elims k es) = Elims (k + 1) (EAApp (tvar 0) : es)
prependForallElim (ECase k es idx a1 es1 a2 es2 elims) = ECase (k + 1) (EAApp (tvar 0) : es) idx a1 es1 a2 es2 elims
prependForallElim (EEx k es a eas elims) = EEx (k + 1) (EAApp (tvar 0) : es) a eas elims

compileFormula :: Formula -> PFormula
compileFormula (Atom a) = PAtom a
compileFormula (Impl a b) = PImpl (a, compileElims a) (compileFormula b)
compileFormula (And a b) = PAnd (compileFormula a) (compileFormula b)
compileFormula phi@(Or a b) = POr phi (compileFormula a) (compileFormula b)
compileFormula (Forall s a) = PForall s (compileFormula a)
compileFormula (Exists s a) = PExists s a (compileFormula a)

compileElims :: Formula -> [Eliminator]
compileElims (Atom a) = [Eliminator {target = a, elims = Elims 0 [], bindersNum = 0, cost = 0}]
compileElims (Impl a b) =
    map (\e -> e{
          elims = prependElim (EApp (compileFormula a)) (elims e)
        , cost = cost e + 10 })
        (compileElims b)
compileElims (And a b) =
    map (\e -> e{elims = prependElim (EProj ILeft) (elims e)}) (compileElims a) ++
    map (\e -> e{elims = prependElim (EProj IRight) (elims e)}) (compileElims b)
compileElims (Or a b) =
    map (\e -> e{ elims = ECase 0 [] ILeft a eas b ebs (elims e)
                , cost = cost e + 10 }) eas ++
    map (\e -> e{ elims = ECase 0 [] IRight b ebs a eas (elims e)
                , cost = cost e + 10 }) ebs
    where
        eas = compileElims a
        ebs = compileElims b
compileElims (Forall _ a) =
    map (\e -> e{ elims = prependForallElim (elims e)
                , bindersNum = bindersNum e + 1
                , cost = cost e +
                    if any (varOccurs (bindersNum e)) (snd (target e)) then 1 else 5 })
        (compileElims a)
compileElims (Exists _ a) =
    map (\e -> e{elims = EEx 0 [] a eas (elims e), bindersNum = bindersNum e + 1}) eas
    where
        eas = compileElims a
