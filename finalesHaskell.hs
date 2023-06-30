--------------------------------------------------------------------------------------
-----------------------------------------2015-----------------------------------------
--------------------------------------------------------------------------------------
-- Definir el tipo de datos de árboles binarios en Haskell, definir la función rev : Tree a -> Tree a, que dado un árbol obtiene el árbol dado vuelta.
data TreeBin a = Nil | Node (TreeBin a) a (TreeBin a) deriving Show

rev :: TreeBin a -> TreeBin a
rev Nil = Nil
rev (Node izq n der) = Node (rev der) n (rev izq)

-- Definir una función que cuente la cantidad de hojas que tiene un árbol.
-- Hoja: Nill a Nill

cantHojas :: TreeBin a -> Int
cantHojas (Node Nil a Nil) = 1
cantHojas (Node Nil a der) = 1+cantHojas der
cantHojas (Node izq a Nil) = 1+cantHojas izq
cantHojas (Node izq a der) = 1+cantHojas izq + cantHojas der

-- Implemente en Haskell la función g : [Int] -> [Int] -> [Int], que dadas dos listas de enteros xs e ys, devuelve una lista la cual en cada posición i contiene la suma del i-ésimo numero par de xs con el i-ésimo numero par de ys, en caso de que alguna de las dos listas no contenga i números pares se debe considerar un 0. 
--  Por ejemplo:	g  [1,2,4,6] [2,2] = [4,6,6]

g :: [Int] -> [Int] -> [Int]
g (x:xs) (y:ys) = res (pares xs) (pares ys)

res [] [] = []
res [x] [] = [x]
res [] [y] = [y]
res [] (y:ys) = [y]++res [] ys
res (x:xs) [] = [x]++res xs []
res (x:xs) (y:ys) = [x+y]++res xs ys

pares [] = []
pares [x]
    | mod x 2 == 0 = [x]
    | otherwise = []
pares (x:xs)
    | (x:xs) == [] = []
    | mod x 2 == 0 = x : pares xs
    | otherwise = pares xs