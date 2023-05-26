--Función super pares
numList :: Int -> [Int]
numList n
    | n > 0 = numList (div n 10)++[mod n 10]
    | otherwise = []

superPares :: Int -> Bool
superPares n = and (map even [x | x <- numList n])

superPares2 :: Int -> Bool
superPares2 n = foldr (&&) True [even x | x <- numList n]

--Pasar arboles a listas, dar pares e impares
data Arbol a = Nill | Node (Arbol a) a (Arbol a) deriving Show

treeList :: Arbol a -> [a]
treeList Nill = []
treeList (Node Nill a Nill) = [a]
treeList (Node izq a Nill) = treeList izq++[a]
treeList (Node Nill a der) = treeList der++[a]
treeList (Node izq a der) = treeList izq++treeList der++[a]

darVuelta :: Arbol a -> Arbol a
darVuelta (Node Nill a Nill) = Node Nill a Nill
darVuelta (Node izq a Nill) = Node Nill a (darVuelta izq)
darVuelta (Node Nill a der) = Node (darVuelta der) a Nill
darVuelta (Node izq a der) = Node (darVuelta der) a (darVuelta izq)

impares :: Integral a => Arbol a -> [a]
impares xs = filter esImpar (treeList xs)

esImpar :: Integral a => a -> Bool
esImpar x
    | mod x 2 /= 0 = True
    | otherwise = False

--Instance Eq, Show, Ord, Num de Nat

--xor estricto, haskell evalua los valores de los argumentos antes de que se
--ejecuten las clausulas correspondientes, es decir, es por casos.
xor :: Bool -> Bool -> Bool
xor True False = True
xor False True = True
xor True True = False
xor False False = False

--xor2 NO es estricto ya evalua de manera perezosa el /=, por lo que no es
--necesario evaluar ambos argumentos.
xor2 :: Bool -> Bool -> Bool
xor2 n m
    | n /= m = True
    | otherwise = False

--Ejercicio 3
enRango :: Int -> Int -> [Int] -> [Int]
enRango a b xs = [x | x <- xs, x >= a, x <= b]

enRango2 :: Int -> Int -> [Int] -> [Int]
enRango2 a b [] = []
enRango2 a b [x]
    | a <= x && b >= x = [x]
    | otherwise = []
enRango2 a b (x:xs)
    | a <= x && b >= x = x:enRango2 a b xs
    | otherwise = enRango2 a b xs

enRango3 :: Int -> Int -> [Int] -> [Int]
enRango3 a b [] = []
enRango3 a b (x:xs)
    | a <= x && b >= x = x:enRango3 a b xs
    | otherwise = enRango3 a b xs

--Ejercicio 4
--4.c
--NORMAL
--False && (trues == trues)
--  [Def. &&]
--False
--
--APLICATIVO
--False && (trues == trues)
--  [Def. trues]
--False && (True:trues == trues)
--  [Def. trues]
--False && (True:(True:trues) == trues)
--  ..., Se va al infinito

--Instanciando Nat
data Nat = Zero | Succ Nat

instance Eq Nat where
    Zero == Zero = True
    Zero == Succ m = False
    Succ n == Succ m = n == m

instance Ord Nat where
    Zero <= _ = True
    _ <= Zero = False
    (Succ n) <= (Succ m) = n <= m

instance Show Nat where
    show Zero = "Zero"
    show (Succ n) = "Succ "++show n

instance Num Nat where
    (+) n Zero = n
    (+) n (Succ m) = Succ (n+m)

    (-) n Zero = n
    (-) Zero _ = error "No se permiten números negativos"
    (-) (Succ n) (Succ m) = n-m

    (*) _ Zero = Zero
    (*) n (Succ m) = n + (n*m)
    
    abs n = n

    signum Zero = Zero
    signum _ = Succ Zero

    fromInteger n
        | n < 0 = error "No se permiten números negativos"
        | n == 0 = Zero
        | otherwise = Succ (fromInteger(n-1))

--Matrices
diagM :: Int -> [(Int, Int)]
diagM n = [(n-i, i) | i <- [0..n]]
matrizInf :: [(Int, Int)]
matrizInf = concat2 [diagM n | n <- [0..]]

concat2 :: [[a]] -> [a]
concat2 [] = []
concat2 [x] = x
concat2 (x:xs) = x++concat2 xs

parMatriz :: [(Int, Int)] -> [(Int, Int)]
parMatriz [] = []
parMatriz (x:xs)
    | mod (fst2 x) 2 == 0 && mod (snd2 x) 2 == 0 = x:parMatriz xs
    | otherwise = parMatriz xs

parMatriz2 :: [(Int, Int)] -> [(Int, Int)]
parMatriz2 xs = [x | x <- xs, mod (fst2 x) 2 == 0, mod (snd2 x) 2 == 0]

imparMatriz :: [(Int, Int)] -> [(Int, Int)]
imparMatriz [] = []
imparMatriz (x:xs)
    | mod (fst2 x) 2 /= 0 && mod (snd2 x) 2 /= 0 = x:imparMatriz xs
    | otherwise = imparMatriz xs

imparMatriz2 :: [(Int, Int)] -> [(Int, Int)]
imparMatriz2 xs = [x | x <- xs, mod (fst2 x) 2 /= 0, mod (snd2 x) 2 /= 0]

fst2 :: (a, a) -> a
fst2 (x, y) = x

snd2 :: (a, a) -> a
snd2 (x, y) = y

--Take and Drop
take2 :: Int -> [a] -> [a]
take2 n [] = []
take2 0 xs = []
take2 n (x:xs) = x:take2 (n-1) xs

drop2 :: Int -> [a] -> [a]
drop2 n [] = []
drop2 0 xs = xs
drop2 n (x:xs) = drop2 (n-1) xs

split2 :: [a] -> [([a], [a])]
split2 xs = [(take2 i xs, drop2 i xs) | i <- [0..length xs]]

tomarMedio :: Int -> Int -> [Int] -> [Int]
tomarMedio a b xs = [x | x <- xs, x >= a && x <= b]

tomarMedio2 :: Int -> Int -> [Int] -> [Int]
tomarMedio2 a b (x:xs) = filter (entre a b) (x:xs)
    where 
        entre a b x
            | a <= x && b >= x = True
            | otherwise = False

diagoM n = [(n-i, i) | i <- [0..n]]
infiM = conca3 [diagoM n | n <- [0..]]
conca3 [] = []
conca3 [x] = x
conca3 (x:xs) = x++conca3 xs

--Operación sobrecargada: Una operación es sobrecargada cuando puede ser aplicada
-- a diferentes tipos de datos y su comportamiento puede variar según el tipo de
-- dato que se le esta aplicando. Se usa en las clases.

--Función polimorfica: Se dice que una función es polimorfica si puede trabajar
-- con cualquier tipo de dato.
-- EJ: id :: a -> a
--     id x = x
--
--     id 5 = 5
--     id "Hola mundo" = "Hola mundo"
--     id True = True















----------------------------------------------------------------------------------

--DEFINICIONES TEORICAS
--  Estricta: una función es estricta en un paramétro si este mismo es un valor
--   definido y no es estricta cuando es una variable ya que tiene que analizarla
--   para dar un resultado.
--
--  Operación sobrecargada: una operación es sobrecargada cuando puede ser aplicada
--   a diferentes tipos de datos y obtener resultados distintos de estos mismos.
--   Esto se da al definilar Class.
--
--  Variable polimorfica: una variable se dice polimorfica si admite varios tipos de
--   valores en su definición.
--   Ej: id :: a -> a
--       id x = x           ----->    id 5 = 5 ------ id "Hola" = "Hola"

--DEFINICIONES FUNCIONES
pFoldl :: (b -> a -> b) -> b -> [a] -> b
pFoldl f z [] = z
pFoldl f z (x:xs) = pFoldl f (f z x) xs

pFoldr :: (a -> b -> b) -> b -> [a] -> b
pFoldr f z [] = z
pFoldr f z (x:xs) = f x (pFoldr f z xs)

--3 DIFERENCIAS
--  DIRECCIÓN: foldl asocia de izquierda a derecha mientras que foldr asocia de
--   derecha a izquierda.
--  TIPO DE PLEGADO: por su tipo de plegado, foldl tiene que analizar todos los
--   elementos de la lista antes de plegarla, mientras que foldr solo analizara el
--   elemento cuando le sea necesario.
--  LISTAS INFINITAS: por su tipo de plegado, foldl no puede realizar listas infinitas
--   ya que primero tendria que evaluar todos sus elementos y no puede, mientras que
--   con foldr podriamos hacerlo con solo encontrar su primer elemento, de ahi pliega
--   hasta el principio de la lista.

--VENTAJAS/DESVENTAJAS FOLDL Y FOLDR
--  Foldl ventajas:
--      -Puede trabajar con otros elementos ademas de listas, como con arboles.
--      -Es mas eficiente al trabajar con operaciones/funciones que asocien a la izq.
--  Foldl desventajas:
--      -No puede trabajar con listas infinitas.
--      -La visualización del foldl resulta compleja al trabajar con grandes listas.
--  Foldr ventajas:
--      -Puede trabajar con listas infinitas.
--      -Es mas eficiente al tener funciones/operaciones que son asociativas a la
--       derecha, como cuando creamos una lista inversa.
--  Foldr desventajas:
--      -No puede trabajar afuera de listas.
--      -Es poco eficiente cuando la función requiere asociación a izquierda.

pMap :: (a -> b) -> [a] -> [b]
pMap f [] = []
pMap f (x:xs) = f x : pMap f xs

pFilter :: (a -> Bool) -> [a] -> [a]
pFilter f [] = []
pFilter f (x:xs)
    | f x = x:pFilter f xs
    | otherwise = pFilter f xs

pZip :: [a] -> [b] -> [(a,b)]
pZip [] ys = []
pZip xs [] = []
pZip (x:xs) (y:ys) = (x,y):pZip xs ys

numToList :: Int -> [Int]
numToList n
    | n>0 = numToList (div n 10)++[mod n 10]
    | otherwise = []

dm :: Int -> [(Int, Int)]
dm n = [(n-i, i) | i <- [0..n]]
mi :: [(Int, Int)]
mi = con [dm n | n <- [0..]]
con :: [[a]] -> [a]
con [] = []
con [x] = x
con (x:xs) = x++con xs

teik :: Int -> [a] -> [a]
teik 0 _ = []
teik n [] = []
teik n (x:xs) = x:teik (n-1) xs

drup :: Int -> [a] -> [a]
drup 0 xs = xs
drup n [] = []
drup n (x:xs) = drup (n-1) xs

fstt :: (a,b) -> a
fstt (x,y) = x

sndd :: (a,b) -> b
sndd (x,y) = y

splitt :: [a] -> [([a],[a])]
splitt xs = [(teik n xs, drup n xs) | n <- [0..length xs]]

or2 :: Bool -> Bool -> Bool
or2 True True = True
or2 True False = True
or2 False True = True
or2 False False = False

or22 :: Bool -> Bool -> Bool
or22 n m
    | n || m = True
    | otherwise = False

xor3 :: Bool -> Bool -> Bool
xor3 True True = False
xor3 True False = True
xor3 False True = True
xor3 False False = False

xor33 :: Bool -> Bool -> Bool
xor33 n m
    | n == m = False
    | otherwise = True

and2 :: Bool -> Bool -> Bool
and2 True True = True
and2 True False = False
and2 False True = False
and2 False False = False

and22 :: Bool -> Bool -> Bool
and22 n m
    | n && m = True
    | otherwise = False

--FUNCIONES DE ALTO ORDEN
supPares n = foldl (&&) True (map even (numList n))
contad n xs = sum [1 | x <- [0..n], x == n]

--MATRICES
paresM n = take n [i | i <- mi, even (fst i), even (snd i)]
imparesM n = take n [i | i <- mi, odd (fst i), odd (snd i)]
mult3 n = take n [i | i <- mi, mod (fst i) 3 == 0, mod (snd i) 3 == 0]

--ARBOLES
darVolta :: Arbol a -> Arbol a
darVolta (Node Nill n Nill) = Node Nill n Nill
darVolta (Node izq n Nill) = Node Nill n (darVolta izq)
darVolta (Node Nill n der) = Node (darVolta der) n Nill
darVolta (Node izq n der) = Node (darVolta der) n (darVolta izq)

listA :: Arbol a -> [a]
listA Nill = []
listA (Node izq n der) = [n]++listA izq++listA der

sumarNodos :: Arbol Int -> Int
sumarNodos Nill = 0
sumarNodos (Node izq n der) = n+sumarNodos izq+sumarNodos der

sumarHojas :: Arbol a -> Int
sumarHojas Nill = 0
sumarHojas (Node Nill n Nill) = 1
sumarHojas (Node izq n der) = sumarHojas izq+sumarHojas der

alturaA :: Arbol a -> Int
alturaA Nill = 0
alturaA (Node Nill n Nill) = 1
alturaA (Node Nill n der) = 1+alturaA der
alturaA (Node izq n Nill) = 1+alturaA izq
alturaA (Node izq n der) = 1+alturaA izq+alturaA der

maxA :: Arbol Int -> Int
maxA Nill = 0
maxA (Node Nill n Nill) = n
maxA (Node izq n der) = max (maxA izq) (maxA der)

tomarMed :: Int -> Int -> [Int] -> [Int]
tomarMed a b [] = []
tomarMed a b xs = [i | i <- xs, i <= b && i >= a]

--INSTANCIAR NAT
--instance Eq Nat where
--  Zero == Zero = True
--  Succ n == Zero = False
--  Succ n == Succ m = n == m
--
--instance Show Nat where
--  show Zero = "Zero"
--  show Succ n = "Succ "++show n
--
--instance Ord Nat where
--  Zero <= Zero = False
--  Succ n <= Zero = False
--  Succ n <= Succ m = n <= m
--
--instance Num Nat where
--  (+) Zero n = n
--  (+) n (Succ m) = Succ (n+m)
--
--  (-) Zero Succ n = error "No hay negativos en los Nat"
--  (-) (Succ n) (Succ m) = if n < m then error "No hay negativos en Nat"
--                          else n-m
--
--  (*) Zero _ = Zero
--  (*) n (Succ m) = n+n*m

-- EVALUACIÓN APLICATIVA, NORMAL, LAZY
-- Dadas las definiciones:
--
-- and :: Bool -> Bool -> Bool
--
-- berr :: Bool
-- berr = False || berr
--
-- trues :: [Bool]
-- trues = True : trues
--
-- xor :: Bool -> Bool -> Bool
--
--PRIMERA: xor berr berr
--NORMAL
--     xor berr berr
--         DEF. BERR
--     xor (False || berr) berr
--         DEF. BERR
--     xor (False || False || berr) berr
--         SE VA AL INFINITO

-- APLICATIVO
--     xor berr berr
--         DEF. BERR
--     xor (False || berr) berr
--         DEF. BERR
--     xor (False || False || berr) berr
--         SE VA AL INFINITO

-- SEGUNDA: foldr (||) berr trues
-- NORMAL
--     foldr (||) berr trues
--         DEF. TRUES
--     foldr (||) berr True:trues
--         DEF. FOLDR
--     True || foldr (||) berr trues
--         DEF. ||
--     True

-- APLICATIVO
--     foldr (||) berr trues
--         DEF. TRUES
--     foldr (||) berr True:trues
--         DEF. FOLDR
--     True || foldr (||) berr trues
--         DEF. TRUES
--     True || foldr (||) berr True:trues
--         SE VA AL INFINITO

-- TERCERA: false && (trues == trues)
-- NORMAL
--     false && (trues == trues)
--         DEF. &&
--     false

-- APLICATIVO
--     false && (trues == trues)
--         DEF. TRUES
--     false && (True:trues == trues)
--         DEF. TRUES
--     false && (True:True:trues == trues)
--         SE VA AL INFINITO