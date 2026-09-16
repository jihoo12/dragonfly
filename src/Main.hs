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

main :: IO ()
main = do
    print identity
    print identityType