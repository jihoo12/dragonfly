module Main (main) where

type Var = Int
type Universe = Int
type Name = String

data Term
    = TVar Var
    | TUniverse Universe
    | Pi Name Term Term
    | Lam Name Term Term
    | App Term Term
    deriving (Eq, Show)

identity :: Term
identity = 
    Lam "A" (TUniverse 0)
        (Lam "x" (TVar 0)
            (TVar 0))

identityType :: Term
identityType = 
    Pi "A" (TUniverse 0)
        (Pi "x" (TVar 0)
            (TVar 1))

shift :: Int -> Int -> Term -> Term
shift d cutoff (TVar k)
    | k >= cutoff = TVar (k + d)
    | otherwise = TVar k

shift _ _ (TUniverse u) = 
    TUniverse u

shift d cutoff (Pi name domain codomain) =
    Pi name
        (shift d cutoff domain)
        (shift d (cutoff + 1) codomain)

shift d cutoff (Lam name ty body) = 
    Lam name 
        (shift d cutoff ty)
        (shift d (cutoff + 1) body)

shift d cutoff (App f x) = 
    App
        (shift d cutoff f)
        (shift d cutoff x)

--subst substitution
--WHNF Weak Head Normal Form


main :: IO ()
main = do
    print "identity and identityType"
    print identity
    print identityType
    print "shift"
    print $ shift 1 0 (TVar 0)
    print $ 
        shift 1 0 $ 
            Lam "x" (TUniverse 0) (TVar 0)