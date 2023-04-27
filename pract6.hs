--Ej 1
data Nat = Zero | Succ Nat deriving Show

--Ej 2
natToInt :: Nat -> Int
natToInt Zero = 0
natToInt (Succ n) =  1+natToInt n

--Ej 3
intToNat :: Int -> Nat
intToNat 0 = Zero
intToNat n = Succ (intToNat (n-1))

--Ej 4
sumaNat :: Nat -> Nat -> Nat
sumaNat x y = intToNat(natToInt(x)+natToInt(y))

--Ej 5
data BinTree a = Nill | Node (BinTree a) a (BinTree a) deriving Show

--Ej 6
sizeTree :: BinTree a -> Int
sizeTree Nill = 0
sizeTree (Node izq _ der) = 1+sizeTree(izq)+sizeTree(der)

--Ej 7
heightTree :: BinTree a -> Int
heightTree Nill = 0
heightTree (Node izq _ der) = max ((heightTree izq)+1) ((heightTree der)+1)
