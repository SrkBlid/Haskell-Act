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