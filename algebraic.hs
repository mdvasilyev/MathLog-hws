{-
 - Автор этого исходника -- Валерий Исаев, копирайт, все дела
 -}

module Algebraic where

import Data.List(intercalate)
import qualified Data.Map as Map
import Control.Monad (forM, guard)

type Sort = String
type Function = String

data Signature = Signature
    { sorts :: [Sort]
    , functions :: [(Function,([Sort],Sort))]
    }

singleSorted :: Sort -> [(Function,Int)] -> Signature
singleSorted sort funs = Signature
    { sorts = [sort]
    , functions = map (\(f,n) -> (f, (replicate n sort, sort))) funs
    }

type Variable = String
data Term = Var Variable Sort | Fun Function [Term]
    deriving Eq

instance Show Term where
    show (Var v _) = v
    show (Fun f ts) = f ++ "(" ++ intercalate ", " (map show ts) ++ ")"

-- Реализуйте функцию, проверяющую что предтерм является корректным термом в данной сигнатуре и возвращающую его сорт, если он корректен.
-- (1 балл.)
isCorrectTerm :: Signature -> Term -> Maybe Sort
isCorrectTerm sig term = case term of
    (Var _ sort) -> if sort `elem` sorts sig
        then Just sort
        else Nothing
    (Fun f ts) -> do
        (argSorts, retSort) <- lookup f (functions sig)
        if length argSorts == length ts
            then do
                argSorts' <- mapM (isCorrectTerm sig) ts
                if argSorts == argSorts'
                    then Just retSort
                    else Nothing
            else Nothing

infix 4 :==
data Formula = Term :== Term
    deriving Eq

instance Show Formula where
    show (t :== t') = show t ++ " = " ++ show t'

data Theory = Theory
    { signature :: Signature
    , axioms :: [Formula]
    }

data Proof = Axiom Formula | Refl Term | Sym Proof | Trans Proof Proof | Cong Function [Proof] | App Proof Variable Term

-- Реализуйте функцию, проверяющую, что доказательство является корректным и возвращающую теорему, которую оно доказывает, если оно корректно.
-- (1 балл.)
isCorrectProof :: Theory -> Proof -> Maybe Formula
isCorrectProof theory proof = case proof of
    Axiom formula -> if formula `elem` axioms theory
        then Just formula
        else Nothing
    Refl term -> case isCorrectTerm (signature theory) term of
        Just sort -> Just (term :== term)
        Nothing -> Nothing
    Sym proof -> case isCorrectProof theory proof of
        Just (f1 :== f2) -> Just (f2 :== f1)
        _ -> Nothing
    Trans proof1 proof2 -> case (isCorrectProof theory proof1, isCorrectProof theory proof2) of
        (Just (f1 :== f2), Just (f2' :== f3)) -> if f2 == f2'
            then Just (f1 :== f3)
            else Nothing
        _ -> Nothing
    Cong function proofs -> do
        (argSorts, retSort) <- lookup function (functions $ signature theory)
        equations <- mapM (isCorrectProof theory) proofs
        guard (length argSorts == length proofs)
        let (lhsTerms, rhsTerms) = unzip [(lhs, rhs) | (lhs :== rhs) <- equations]
        argSortsLhs <- mapM (isCorrectTerm (signature theory)) lhsTerms
        argSortsRhs <- mapM (isCorrectTerm (signature theory)) rhsTerms
        guard (argSortsLhs == argSorts)
        guard (argSortsRhs == argSorts)
        return (Fun function lhsTerms :== Fun function rhsTerms)
    App proof var term -> do
        (t1 :== t2) <- isCorrectProof theory proof
        termSort <- isCorrectTerm (signature theory) term
        let substitute v t (Var v' s) | v == v' = t
                                      | otherwise = Var v' s
            substitute v t (Fun f ts) = Fun f (map (substitute v t) ts)
        let newT1 = substitute var term t1
        let newT2 = substitute var term t2
        return (newT1 :== newT2)

-- Пример

var x = Var x "D"
x *. y = Fun "*" [x,y]
inv x = Fun "inv" [x]
e = Fun "1" []

assoc = (var "x" *. var "y") *. var "z" :== var "x" *. (var "y" *. var "z")
e_left = e *. var "x" :== var "x"
e_right = var "x" *. e :== var "x"
inv_left = inv (var "x") *. var "x" :== e

groupTheory :: Theory
groupTheory = Theory
    { signature = singleSorted "D" [("*",2), ("1",0), ("inv",1)]
    , axioms = [assoc, e_right, e_left, inv_left]
    }

-- Пример доказательства в нашем формализме
-- Вспомогательная функция, которая по цепочке доказательств p_1: t_1 = t_2, p_2: t_2 = t_3, .., p_n : t_{n} = t_{n + 1}
-- возвращает доказательство t_{1} = t_{n + 1}
trans :: [Proof] -> Proof
trans [p] = p
trans (p:ps) = Trans p (trans ps)

-- Если p доказывает y * y = y, то (idempotent_is_identity y p) доказывает, что y = 1.
idempotent_is_identity :: Term -> Proof -> Proof
idempotent_is_identity y p = trans
    [ Sym $ App (Axiom e_left) "x" y                            -- y = 1 * y
    , Cong "*" [Sym $ App (Axiom inv_left) "x" y, Refl y]       -- 1 * y = (inv(y) * y) * y
    , App (App (App (Axiom assoc) "x" (inv y)) "y" y) "z" y     -- (inv(y) * y) * y = inv(y) * (y * y)
    , Cong "*" [Refl $ inv y, p]                                -- inv(y) * (y * y) = inv(y) * y
    , App (Axiom inv_left) "x" y                                -- inv(y) * y = 1
    ]

-- inv_right доказывает, что (x * inv x = 1).
inv_right :: Proof
inv_right = idempotent_is_identity (x *. inv x) $ trans
    [ App (App (Axiom assoc) "y" (inv x)) "z" (x *. inv x)                                                  -- (x * inv(x)) * (x * inv(x)) = x * (inv(x) * (x * inv(x)))
    , Cong "*" [Refl x, Sym $ App (App (App (Axiom assoc) "x" (inv x)) "y" x) "z" (inv x)]                  -- x * (inv(x) * (x * inv(x))) = x * ((inv(x) * x) * inv(x))
    , Cong "*" [Refl x, Trans (Cong "*" [Axiom inv_left, Refl $ inv x]) $ App (Axiom e_left) "x" (inv x)]   -- x * ((inv(x) * x) * inv(x)) = x * inv(x)
    ]
  where
    x = var "x"

-- Докажите, что inv(inv(x)) = x
-- (2 балла.)
inverse_is_idempotent :: Proof
inverse_is_idempotent = Trans
    (Trans
        (Sym $ App (Axiom e_right) "x" (inv (inv (var "x"))))
        (Trans
            (Sym $ Cong "*" [Refl (inv (inv (var "x"))), Axiom inv_left])
            (Sym $ App (App (App (Axiom assoc) "x" (inv (inv (var "x")))) "y" (inv (var "x"))) "z" (var "x"))
        )
    )
    (Trans
        (Cong "*" [App (Axiom inv_left) "x" (inv $ var "x"), Refl $ var "x"])
        (Axiom e_left)
    )


main = do
    print (isCorrectProof groupTheory inv_right)
    print (isCorrectProof groupTheory inverse_is_idempotent)
