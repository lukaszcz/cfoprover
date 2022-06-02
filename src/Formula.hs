{-# LANGUAGE DeriveTraversable, FlexibleInstances #-}
module Formula where

import Data.Functor
import Data.Bifunctor
import Data.List as List
import Data.List.Extras.Pair

import Control.Monad
import Control.Unification
import Control.Unification.IntVar

{------------------------------------}
{- Terms, formulas, proof terms -}

type Symbol = Int

data TermF t = Var Symbol | Fun Symbol [t] deriving (Eq, Functor, Foldable, Traversable)

instance Unifiable TermF where
    zipMatch (Var x) (Var y)
        | x == y = Just $ Var x
    zipMatch (Fun f1 args1) (Fun f2 args2)
        | f1 == f2 = fmap (Fun f1) (pairWith (curry Right) args1 args2)
    zipMatch _ _ = Nothing

type Term = UTerm TermF IntVar

instance Eq Term where
    UVar v1 == UVar v2 = v1 == v2
    UTerm t1 == UTerm t2 = t1 == t2
    _ == _ = False

tvar :: Symbol -> Term
tvar x = UTerm $ Var x

tfun :: Symbol -> [Term] -> Term
tfun f args = UTerm $ Fun f args

toccurs :: Symbol -> Term -> Bool
toccurs _ (UVar _) = False
toccurs s (UTerm (Var x)) = s == x
toccurs s (UTerm (Fun _ ts)) = any (toccurs s) ts

tmaxSymbol :: Term -> Symbol
tmaxSymbol (UVar _) = 0
tmaxSymbol (UTerm (Var x)) = x
tmaxSymbol (UTerm (Fun s ts)) = foldr (max . tmaxSymbol) s ts

type Atom = (Symbol, [Term])

data Formula = Atom Atom
            | Impl Formula Formula
            | And Formula Formula
            | Or Formula Formula
            | Forall Symbol Formula
            | Exists Symbol Formula

occurs :: Symbol -> Formula -> Bool
occurs s (Atom (_, args)) = any (toccurs s) args
occurs s (Impl a b) = occurs s a || occurs s b
occurs s (And a b) = occurs s a || occurs s b
occurs s (Or a b) = occurs s a || occurs s b
occurs s (Forall s' a) | s /= s' = occurs s a
occurs s (Exists s' a) | s /= s' = occurs s a
occurs _ _ = False

maxSymbol :: Formula -> Symbol
maxSymbol (Atom (s, args)) = foldr (max . tmaxSymbol) s args
maxSymbol (Impl a b) = max (maxSymbol a) (maxSymbol b)
maxSymbol (And a b) = max (maxSymbol a) (maxSymbol b)
maxSymbol (Or a b) = max (maxSymbol a) (maxSymbol b)
maxSymbol (Forall s a) = max s (maxSymbol a)
maxSymbol (Exists s a) = max s (maxSymbol a)

data Idx = ILeft | IRight

data Elim p = EApp p | EAApp Term | EProj Idx

class Substitutable a where
    subst :: [(Symbol,Term)] -> a -> a

csubst :: Substitutable a => [(Symbol,Term)] -> a -> a
csubst [] x = x
csubst env x = subst env x

instance Substitutable Term where
    subst env (UTerm (Var x)) | Just y <- lookup x env = y
    subst env (UTerm (Fun f args)) = UTerm $ Fun f (map (subst env) args)
    subst _ t = t

instance Substitutable Formula where
    subst env (Atom (s, args)) = Atom (s, map (subst env) args)
    subst env (Impl a b) = Impl (subst env a) (subst env b)
    subst env (And a b) = And (subst env a) (subst env b)
    subst env (Or a b) = Or (subst env a) (subst env b)
    subst env (Forall x phi) = Forall x (csubst env' phi)
        where env' = filter (not . (==) x . fst) env
    subst env (Exists x phi) = Exists x (csubst env' phi)
        where env' = filter (not . (==) x . fst) env

instance Eq Formula where
    (Atom (s1, args1)) == (Atom (s2, args2)) = s1 == s2 && args1 == args2
    (Impl a1 b1) == (Impl a2 b2) = a1 == a2 && b1 == b2
    (And a1 b1) == (And a2 b2) = a1 == a2 && b1 == b2
    (Or a1 b1) == (Or a2 b2) = a1 == a2 && b1 == b2
    (Forall s1 a1) == (Forall s2 a2) =
        not (occurs s1 a2) && a1 == subst [(s2,tvar s1)] a2
    (Exists s1 a1) == (Exists s2 a2) =
        not (occurs s1 a2) && a1 == subst [(s2,tvar s1)] a2
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
    mkExIntro :: Symbol -> Formula -> Term -> p -> p
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
    mkExIntro _ _ _ _ = ()
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
           | ExIntro Symbol Formula Term PTerm -- ExIntro s a tt t :: Exists s a
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
mapTerms f (ExIntro s phi t x) =  do
    x' <- mapTerms f x
    t' <- f t
    return $ ExIntro s phi t' x'
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
    return (Forall s a)
infer' env (AApp t tt) = do
    a <- infer' env t
    case a of
        Forall s a' -> return $ subst [(s,tt)] a'
        _ -> Nothing
infer' env (ExIntro s a tt t) = do
    a' <- infer' env t
    guard $ subst [(s,tt)] a == a'
    return $ Exists s a
infer' env (ExElim t t') = do
    a <- infer' env t
    case a of
        Exists s a' -> do
            b <- infer' env t'
            case b of
                Forall s' (Impl b1 b2) | b1 == subst [(s,tvar s')] a' -> return b2
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

data CElim =
      Elims [Elim PFormula]
    | ECase [Elim PFormula] Idx Formula [Eliminator] Formula [Eliminator]
    | EEx [Elim PFormula] Symbol Formula [Eliminator]

data Eliminator = Eliminator {
      target :: Atom
    , elims :: [CElim]
    , evars :: [Symbol]
    , cost :: Int
    }

data PFormula = PAtom Atom
              | PImpl (Formula, [Eliminator]) PFormula
              | PAnd PFormula PFormula
              | POr Formula PFormula PFormula
              | PForall Symbol PFormula
              | PExists Symbol Formula PFormula

instance Substitutable (Elim PFormula) where
    subst env (EApp phi) = EApp (subst env phi)
    subst env (EAApp t) = EAApp (subst env t)
    subst _ x@(EProj _) = x

instance Substitutable CElim where
    subst env (Elims es) = Elims $ map (subst env) es
    subst env (ECase es idx a1 es1 a2 es2) =
        ECase (map (subst env) es) idx (subst env a1) (map (subst env) es1)
                (subst env a2) (map (subst env) es2)
    subst env (EEx es s a eas) =
        EEx (map (subst env) es) s (subst env' a) (map (subst env') eas)
        where env' = filter ((/=) s . fst) env

instance Substitutable Eliminator where
    subst env e = e { target = second (map (subst env)) (target e)
                    , elims = map (subst env) (elims e) }

instance Substitutable PFormula where
    subst env (PAtom (p, args)) = PAtom (p, map (subst env) args)
    subst env (PImpl e phi) = PImpl (second (map (subst env)) e) (subst env phi)
    subst env (PAnd phi1 phi2) = PAnd (subst env phi1) (subst env phi2)
    subst env (POr phi phi1 phi2) = POr phi (subst env phi1) (subst env phi2)
    subst env (PForall x phi) = PForall x (csubst env' phi)
        where env' = filter ((/=) x . fst) env
    subst env (PExists x a phi) = PExists x a (csubst env' phi)
        where env' = filter ((/=) x . fst) env

prependElim :: Elim PFormula -> [CElim] -> [CElim]
prependElim e [] = [Elims [e]]
prependElim e (Elims es : elims) = Elims (e : es) : elims
prependElim e (ECase es idx a1 es1 a2 es2 : elims) = ECase (e : es) idx a1 es1 a2 es2 : elims
prependElim e (EEx es s a eas : elims) = EEx (e : es) s a eas : elims

compileFormula :: Formula -> PFormula
compileFormula (Atom a) = PAtom a
compileFormula (Impl a b) = PImpl (a, compileElims a) (compileFormula b)
compileFormula (And a b) = PAnd (compileFormula a) (compileFormula b)
compileFormula phi@(Or a b) = POr phi (compileFormula a) (compileFormula b)
compileFormula (Forall s a) = PForall s (compileFormula a)
compileFormula (Exists s a) = PExists s a (compileFormula a)

compileElims :: Formula -> [Eliminator]
compileElims (Atom a) = [Eliminator {target = a, elims = [], evars = [], cost = 0}]
compileElims (Impl a b) =
    map (\e -> e{
          elims = prependElim (EApp (compileFormula a)) (elims e)
        , cost = cost e + 10 })
        (compileElims b)
compileElims (And a b) =
    map (\e -> e{elims = prependElim (EProj ILeft) (elims e)}) (compileElims a) ++
    map (\e -> e{elims = prependElim (EProj IRight) (elims e)}) (compileElims b)
compileElims (Or a b) =
    map (\e -> e{ elims = ECase [] ILeft a eas b ebs : elims e
                , cost = cost e + 10 }) eas ++
    map (\e -> e{ elims = ECase [] IRight b ebs a eas : elims e
                , cost = cost e + 10 }) ebs
    where
        eas = compileElims a
        ebs = compileElims b
compileElims (Forall s a) =
    map (\e -> e{ evars = s : evars e
                , cost = cost e +
                    if any (toccurs s) (snd (target e)) then 1 else 5 })
        (compileElims a)
compileElims (Exists s a) =
    map (\e -> e{elims = EEx [] s a eas : elims e}) eas
    where
        eas = compileElims a
