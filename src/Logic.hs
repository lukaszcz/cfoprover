{-# LANGUAGE DeriveTraversable, FlexibleInstances #-}
module Logic where

import Data.List.Extras.Pair

import Control.Unification
import Control.Unification.IntVar

{------------------------------------}
{- Terms, formulas, proof terms -}

type Symbol = Int

data TermF t = Var Symbol | Fun Symbol [t] deriving (Functor, Foldable, Traversable)

instance Unifiable TermF where
    zipMatch (Var x) (Var y)
        | x == y = Just $ Var x
    zipMatch (Fun f1 args1) (Fun f2 args2)
        | f1 == f2 = fmap (Fun f1) (pairWith (\l r -> Right (l,r)) args1 args2)
    zipMatch _ _ = Nothing

type Term = UTerm TermF IntVar

tvar :: Symbol -> Term
tvar x = UTerm $ Var x

tfun :: Symbol -> [Term] -> Term
tfun f args = UTerm $ Fun f args

type Atom = (Symbol, [Term])

data Formula = Atom Atom
             | Impl Formula Formula
             | And Formula Formula
             | Or Formula Formula
             | Forall Symbol Formula
             | Exists Symbol Formula

data Idx = ILeft | IRight

data Elim p = EApp p | EProj Idx

class Substitutable a where
    subst :: [(Symbol,Term)] -> a -> a

csubst :: Substitutable a => [(Symbol,Term)] -> a -> a
csubst [] x = x
csubst env x = subst env x

instance Substitutable Term where
    subst env (UTerm (Var x)) | Just y <- lookup x env = y
    subst env (UTerm (Fun f args)) = UTerm $ Fun f (map (subst env) args)
    subst _ t = t

class Proof p where
    mkVar :: Symbol -> p
    mkLam :: Symbol -> Formula -> p -> p
    mkApp :: p -> p -> p
    mkConj :: p -> p -> p
    mkProj :: Idx -> p -> p
    mkInj :: Idx -> p -> p
    mkCase :: p -> p -> p
    mkALam :: Symbol -> p -> p
    mkAApp :: p -> Term -> p
    mkExIntro :: Term -> p -> p
    mkExElim :: p -> p
    mkElim :: Symbol -> [Elim p] -> p
    mkElim s elims = mk (mkVar s) elims
        where
          mk p [] = p
          mk p (EApp p' : es) = mk (mkApp p p') es
          mk p (EProj i : es) = mk (mkProj i p) es

instance Proof () where
    mkVar _ = ()
    mkLam _ _ _ = ()
    mkApp _ _ = ()
    mkConj _ _ = ()
    mkProj _ _ = ()
    mkInj _ _ = ()
    mkCase _ _ = ()
    mkALam _ _ = ()
    mkAApp _ _ = ()
    mkExIntro _ _ = ()
    mkExElim _ = ()
    mkElim _ _ = ()

data PTerm = PVar Symbol
           | Lambda Symbol Formula PTerm
           | App PTerm PTerm
           | Conj PTerm PTerm
           | Proj Idx PTerm
           | Inj Idx PTerm
           | Case PTerm PTerm
           | ALambda Symbol PTerm
           | AApp PTerm Term
           | ExIntro Term PTerm
           | ExElim PTerm

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

{------------------------------------}
{- Optimized formula representation -}

data CElim = Elims [Elim PFormula] | ECase Idx Eliminator PFormula | EEx

data Eliminator = Eliminator {
      target :: Atom
    , elims :: [CElim]
    , evars :: [Symbol]
    , cost :: Int
    }

data PFormula = PAtom Atom
              | PImpl Eliminator PFormula
              | PAnd PFormula PFormula
              | POr PFormula PFormula
              | PForall Symbol PFormula
              | PExists Symbol PFormula

instance Substitutable (Elim PFormula) where
    subst env (EApp phi) = EApp (subst env phi)
    subst _ x@(EProj _) = x

instance Substitutable CElim where
    subst env (Elims es) = Elims $ map (subst env) es
    subst env (ECase idx e phi) = ECase idx (subst env e) (subst env phi)
    subst _ EEx = EEx

instance Substitutable Eliminator where
    subst env e = e { target = (fst $ target e, map (subst env) $ snd $ target e)
                    , elims = map (subst env) (elims e) }

instance Substitutable PFormula where
    subst env (PAtom (p, args)) = PAtom (p, (map (subst env) args))
    subst env (PImpl e phi) = PImpl (subst env e) (subst env phi)
    subst env (PAnd phi1 phi2) = PAnd (subst env phi1) (subst env phi2)
    subst env (POr phi1 phi2) = POr (subst env phi1) (subst env phi2)
    subst env (PForall x phi) = PForall x (csubst env' phi)
        where env' = filter (not . ((==) x) . fst) env
    subst env (PExists x phi) = PExists x (csubst env' phi)
        where env' = filter (not . ((==) x) . fst) env
