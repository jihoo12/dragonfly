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

main :: IO ()
main = putStrLn "Hello, Haskell!"
