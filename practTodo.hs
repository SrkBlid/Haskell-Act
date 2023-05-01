-------------------------PRÁCTICO 1-------------------------

--2
--head(tail("hola mundo"))

--3
--reverse(head("hola mundo"))

--5
--mod (head(reverse([1,2,3]))) 2 == 0

--6
--mod (sum [1,2,3]) 3 == 0

--7
--mod (sum [1,2,3]) 3 == 0 || mod (sum [1,2,3]) 6 == 0

--8
list :: Int -> [Int]
list 0 = []
list n = list (div n 10) ++ [mod n 10]

--9
--reverse("olo") == "olo"

-------------------------PRÁCTICO 2-------------------------

--2
hd :: [a] -> a
hd [] = error "Lista vacia"
hd (x:xs) = x

tl :: [a] -> [a]
tl [] = error "Lista vacia"
tl (x:xs) = xs

last2 :: [a] -> a
last2 [] = error "Lista vacia"
last2 [x] = x
last2 (x:xs) = last2 xs

last3 :: [a] -> a
last3 [] = error "Lista vacia"
last3 xs = head(reverse xs)

init2 :: [a] -> [a]
init2 [] = error "Lista vacia"
init2 [x] = []
init2 (x:xs) = x:init2 xs 

--3
maxTres :: Int -> Int -> Int -> Int
maxTres x y z
    |x>=y && x>=z = x
    |y>=x && y>=z = y
    |z>=x && z>=y = z

--4
concatenar :: [a] -> [a] -> [a]
concatenar xs [] = xs
concatenar [] ys = ys
concatenar xs (y:ys) = y:concatenar xs ys

tomar :: Int -> [a] -> [a]
tomar 0 _ = []
tomar _ [] = []
tomar n (x:xs) = x:tomar (n-1) xs

tirar :: Int -> [a] -> [a]
tirar 0 xs = xs
tirar _ [] = []
tirar n (x:xs) = tirar (n-1) xs

concaF :: [a] -> [a] -> [a]
concaF xs [] = xs
concaF [] ys = ys
concaF xs ys = xs++ys

concaF2 :: [a] -> [a] -> [a]
concaF2 xs [] = xs
concaF2 [] ys = ys
concaF2 (x:xs) ys = x:concaF xs ys

--5
abs2 :: Int -> Int
abs2 0 = 0
abs2 n
    |n > 0 = n
    |otherwise = -n

--6
edad :: (Int, Int, Int) -> (Int, Int, Int) -> Int
edad (n1,n2,n3) (m1,m2,m3) = abs2(n3-m3)

--7
xor2 :: Bool -> Bool -> Bool
xor2 n m
    | n && m = False
    | n && not m = True
    | not n && m = True
    | not n && not m = False

xor3 :: Bool -> Bool -> Bool
xor3 n m
    | (n && not m) || (not n && m) = True
    | otherwise = False

--8
esPrimo :: Int -> Bool
esPrimo n 
    | cantDivs n 1 >= 2 = False
    | cantDivs n 1 < 2 = True
    where cantDivs n i
            | n == i = 0
            | mod n i == 0 = 1+cantDivs n (i+1)
            | otherwise = cantDivs n (i+1)

--9
listPrimos :: Int -> [Int]
listPrimos 0 = []
listPrimos n = if esPrimo(n) then listPrimos (n-1)++[n] else listPrimos (n-1)

--10
reversaLista :: [Int] -> [Int]
reversaLista [] = []
reversaLista (x:xs) = reversaLista xs ++ [x]

--11
listasIguales :: [Int] -> [Int] -> Bool
listasIguales [] [] = True
listasIguales _ [] = False
listasIguales [] _ = False
listasIguales (x:xs) (y:ys)
    | x /= y = False
    | otherwise = listasIguales xs ys

--12
listPalindroma :: Eq a => [a] -> Bool
listPalindroma [] = True
listPalindroma [x] = True
listPalindroma (x:xs)
    | x == head(reverse xs) = listPalindroma (init xs)
    | otherwise = False

--13
raicesR :: Int -> Int -> Int -> Int
raicesR a b c = 
        if b*b-4*a*c == 0 then
                1
        else
                2

-------------------------PRÁCTICO 3-------------------------

--1
mergeLT :: Ord a => [a] -> [a] -> [(a, a)]
mergeLT [] [] = []
mergeLT [] _ = error "Las listas no tienen el mismo tamaño"
mergeLT _ [] = error "Las listas no tienen el mismo tamaño"
mergeLT (x:xs) (y:ys) = [(x,y)]++mergeLT xs ys 

mergeL :: Ord a => [a] -> [a] -> [a]
mergeL [] [] = []
mergeL [] _ = error "Las listas no tienen el mismo tamaño"
mergeL _ [] = error "Las listas no tienen el mismo tamaño"
mergeL (x:xs) (y:ys) = [x]++[y]++mergeL xs ys 

--2
ordInt :: [Int] -> [Int]
ordInt [] = []
ordInt (x:xs) = mayor x (ordInt xs)


mayor :: Int -> [Int] -> [Int]
mayor x [] = [x]
mayor x (y:ys)
    | x <= y = x: y: ys
    | otherwise = y:mayor x ys

--3
dosN :: Int -> Int
dosN 0 = 1
dosN n = 2*dosN (n-1) 

--4
secBinaria :: Int -> [Int]
secBinaria 0 = []
secBinaria n 
    | mod n 2 == 1 = secBinaria (div n 2) ++ [1]
    | otherwise = secBinaria (div n 2) ++ [0]

--5
binPar :: [Int] -> Bool
binPar [] = True
binPar xs 
    | last xs == 0 = True
    | otherwise = False

--6
distHamming :: String -> String -> Int
distHamming [] _ = 0
distHamming _ [] = 0
distHamming (x:xs) (y:ys)
    | x /= y = 1+distHamming xs ys
    | otherwise = distHamming xs ys

--7
cuadPerf :: Int -> Bool
cuadPerf n = sqrt(fromIntegral n) == fromIntegral(round(sqrt(fromIntegral n)))

--8
repes :: Eq a => Int -> a -> [a] -> Bool
repes 0 _ _ = True
repes _ _ [] = False
repes n z xs
    | contador n z xs 0 == n = True
    | contador n z xs 0 /= n = False

contador :: Eq a => Int -> a -> [a] -> Int -> Int
contador 0 _ _  i = 0
contador _ _ [] i = i
contador n z (x:xs) i
    | z == x = contador n z xs (i+1)
    | z /= x = contador n z xs i

--9
nelem :: Eq a => [a] -> Int -> a
nelem [] _ = error "Lista vacia"
nelem (x:xs) n = pos (x:xs) n 0
    where pos (x:xs) n i
            | n /= i = pos xs n (i+1)
            | otherwise = x

--10
posicionesC2 :: String -> Char -> [Int]
posicionesC2 [] _ = []
posicionesC2 (x:xs) c = posicionesC2' (x:xs) c 0
    where 
        posicionesC2' :: String -> Char -> Int -> [Int]
        posicionesC2' [] c i = []
        posicionesC2' [x] c i
            | x == c = [i]
            | otherwise = posicionesC2' [] c (i+1)
        posicionesC2' (x:xs) c i
            | x == c = i:posicionesC2' xs c (i+1)
            | otherwise = posicionesC2' xs c (i+1) 

posicionesC'' :: [Char] -> Char -> [Int]
posicionesC'' (x:xs) c = [i | (x,i) <- zip (x:xs) [0..], c == x]

--11
compact2 :: Eq a => [a] -> [a]
compact2 [] = []
compact2 [x] = [x]
compact2 (x:xs)
    | x == head(xs) = compact2 xs
    | otherwise = x:compact2 xs

-------------------------PRÁCTICO 4-------------------------

--1
--cuadrado :: Int -> Int
--cuadrado x = x*x
--
--head :: [a] -> a
--head (x:xs) = x
--
--APLICATIVO
--2*cuadrado(head[2,4,5,6,7,8])
--DEFINICIÓN HEAD
--2*cuadrado(2)
--DEFINICIÓN CUADRADO
--2*2*2
--ARITMETICA
--8
--Cantidad de reducciones: 3
--
--NORMAL
--2*cuadrado(head[2,4,5,6,7,8])
--DEFINICIÓN CUADRADO
--2*(head[2,4,5,6,7,8])*(head[2,4,5,6,7,8])
--DEFINICIÓN HEAD
--2*(2)*(head[2,4,5,6,7,8])
--DEFINICIÓN HEAD
--2*(2)*(2)
--ARITMETICA
--8
--Cantidad de reducciones: 4

--2
--linf = 1:linf
--
--APLICATIVO
--head.linf
--DEFINICIÓN LINF
--head(1:linf)
--DEFINICIÓN LINF
--head(1:1:linf)
-- ...
--Cantidad de reducciones: Infinitas
--
--NORMAL
--head.linf
--DEFINICIÓN LINF
--head(1:linf)
--DEFINICIÓN HEAD
--1
--Cantidad de reducciones: 2

--3
-- f :: Int -> Int -> Int
-- f x 0 = x
-- f x (n+1) = cuadrado (f x n)
--
--APLICATIVO
--f.2.3
--DEFINICIÓN F
--cuadrado(f 2 2)
--DEFINICIÓN F
--cuadrado(cuadrado(f 2 1))
--DEFINICIÓN F
--cuadrado(cuadrado(cuadrado(f 2 0)))
--DEFINICIÓN F
--cuadrado(cuadrado(cuadrado(2)))
--DEFINICIÓN CUADRADO
--cuadrado(cuadrado(2*2))
--ARITMETICA
--cuadrado(cuadrado(4))
--DEFINICIÓN CUADRADO
--cuadrado(4*4)
--ARITMETICA
--cuadrado(16)
--DEFINICIÓN CUADRADO
--16*16
--ARITMETICA
--256
--Cantidad de reducciones: 10
--
--NORMAL
--f.2.3
--DEFINICIÓN F
--cuadrado(f 2 2)
--DEFINICIÓN CUADRADO
--(f 2 2)(f 2 2)
--DEFINICIÓN F
--(cuadrado(f 2 1))(f 2 2)
--DEFINICIÓN CUADRADO
--((f 2 1)(f 2 1))(f 2 2)
--DEFINICIÓN F
--((cuadrado(f 2 0))(f 2 1))(f 2 2)
--DEFINICIÓN CUADRADO
--(((f 2 0)(f 2 0))(f 2 1))(f 2 2)
--DEFINICIÓN F
--((2*(f 2 0)))(f 2 1))(f 2 2)
--DEFINICIÓN F
--((2*2))(f 2 1))(f 2 2)
--ARITMETICA
--(4*(f 2 1))(f 2 2)
--DEFINICIÓN F
--(4*(cuadrado(f 2 0)))(f 2 2)
--DEFINICIÓN CUADRADO
--(4*((f 2 0)(f 2 0)))(f 2 2)
--DEFINICIÓN F
--(4*2*(f 2 0))(f 2 2)
--ARITMETICA
--(8*(f 2 0))(f 2 2)
--DEFINICIÓN F
--(8*2)(f 2 2)
--ARITMETICA
--16*(f 2 2)
--DEFINICIÓN F
--16*(cuadrado (f 2 1))
--DEFINICIÓN CUADRADO
--16*((f 2 1)(f 2 1))
--DEFINICIÓN F
--16*((cuadrado (f 2 0))(f 2 1))
--DEFINICIÓN CUADRADO
--16*((f 2 0)(f 2 0))(f 2 1))
--DEFINICIÓN F
--16*(2*(f 2 0))(f 2 1))
--DEFINICIÓN F
--16*((2*2)(f 2 1))
--ARITMETICA
--16*(4*(f 2 1))
--DEFINICIÓN F
--16*(4*(cuadrado(f 2 0)))
--DEFINICIÓN CUADRADO
--16*(4*((f 2 0)(f 2 0)))
--DEFINICIÓN F
--16*(4*(2*(f 2 0)))
--DEFINICIÓN F
--16*(4*(2*2))
--ARITMETICA
--16*(4*4)
--ARITMETICA
--16*16
--ARITMETICA
--256
--Cantidad de reducciones: 29

--4
--square :: Int -> Int
--square x = x*x
--
--inf :: Int
--inf = inf+1
--
--APLICATIVO
--square.inf
--DEFINICIÓN INF
--square(inf+1)
--DEFINICIÓN INF
--square((inf+1)+1)
-- ...
--Cantidad de reducciones: Infinitas
--
--NORMAL
--square.inf
--DEFINICIÓN SQUARE
--inf.inf
--DEFINICIÓN INF
--(inf+1).inf
--DEFINICIÓN INF
--((inf+1)+1).inf
-- ...
--Cantidad de reducciones: Infinitas

--5
--LAZY
--f.2.3
--DEFINICIÓN F
--cuadrado(f 2 2)
--  [cuadrado = x*x]
--x*x
--  [x = f 2 2]
--DEFINICIÓN F
--(cuadrado (f 2 1))*x
--  [y = f 2 1]
--(y*y)*x
--DEFINICIÓN F
--((cuadrado (f 2 0))*y)*x
--  [z = f 2 0]
--((z*z)*y)*x
--Z = 2
--((2*z)*y)*x
--Z = 2
--((2*2)*y)*x
--ARITMETICA
--(4*y)*x
--Y= Z*Z
--(4*(2*2))*x
--ARITMETICA
--(4*4)*x
--ARITMETICA
--16*x
--X= Y*Y
--16*(4*4)
--ARITMETICA
--16*16
--ARITMETICA
--256
--Cantidad de reducciones: 16

--6
--Se puede cambiar el orden evaluativo de Haskell pero solo temporalmente con el
-- $!, esto puede servir para obligar a evaluar ciertas expresiones.
-- EJ: f $! x = x+1

-------------------------PRÁCTICO 5-------------------------
--1
--[1..]

listInf :: [Int]
listInf = [1..]

--2
listInfN :: Int -> [Int]
listInfN n = [n..]

--3
listHastaN :: Int -> [Int]
listHastaN 0 = []
listHastaN n = [1..n]

--4
ret5 :: [Int] -> [Int]
ret5 = take 5

--5
retCuad :: [Int] -> [Int]
retCuad xs = map (^2) [n | n <- xs]

--6
listDivs :: Int -> [Int]
listDivs n = filter (esDivisor n) [x | x <- [1..n]]
esDivisor :: Int -> Int -> Bool
esDivisor n x
    | mod n x == 0 = True
    | otherwise = False

--7
primosInt :: [Int] -> [Int]
primosInt (x:xs) = filter esPrimo2 (x:xs)
esPrimo2 :: Int -> Bool
esPrimo2 n
    | length [x | x <- [1..n], mod n x == 0] > 2 = False
    | otherwise = True

--8
sumCuads :: [Int] -> Int
sumCuads xs = sum(map (^2) xs)

--9
sucesores :: [Int] -> [Int]
sucesores xs = map (+1) xs

--10
sumar :: [Int] -> Int
sumar xs = foldr (+) 0 xs 

--11
factF :: Int -> Int
factF n = foldr (*) 1 [1..n]

--12
andF :: [Bool] -> Bool
andF xs = foldr (&&) True xs

--13
op :: a -> Int
op n = 1
tamFl :: [a] -> Int
tamFl xs = foldl (+) 0 (map (op) xs)
tamFr :: [a] -> Int
tamFr xs = foldr (+) 0 (map (op) xs)

--14
sucesoresL :: [Int] -> [Int]
sucesoresL xs = [n+1 | n <- xs]

--15
cuadradosL :: [Int] -> [Int]
cuadradosL xs = [n^2 | n <- xs]

--16
may10 :: [Int] -> [Int]
may10 xs = [i | i <- xs, i > 10]

--17
divisoresL :: Int -> [Int]
divisoresL n = [i | i <- [1..n], mod n i == 0]

--18
todosOcurrenEn2 :: Eq a => [a] -> [a] -> Bool
todosOcurrenEn2 [] _ = False
todosOcurrenEn2 _ [] = False
todosOcurrenEn2 xs ys = and [elem n ys | n <- xs]

--19
primos2N :: Int -> [Int]
primos2N n = 1:[i | i <- [2..n], esPrimo(i)]

--20
prodCart :: [Int] -> [Int] -> [(Int, Int)]
prodCart xs ys = [(n,m) | n <- xs, m <- ys]

--21
ocurrenciasX :: Eq a => [a] -> a -> Int
ocurrenciasX xs n = length [1 | i <- xs, i == n]

--22
split4 :: [a] -> [([a],[a])]
split4 xs = [(take n xs, drop n xs) | n <- [0..length xs]]

--23
sumaSeg2 :: [Int] -> Int
sumaSeg2 xs = sum [sum (take i xs) | i <- [0..length xs]]

--24
infPares2 :: [Int]
infPares2 = [i | i <- [0..], mod i 2 == 0]

--Práctico 6--
--1
data Nat = Zero | Succ Nat deriving Show

--2
natToInt2 :: Nat -> Int
natToInt2 Zero = 0
natToInt2 (Succ n) = 1+natToInt2 n

--3
intToNat2 :: Int -> Nat
intToNat2 0 = Zero
intToNat2 n = Succ (intToNat2 (n-1))

--4
sumaNat :: Nat -> Nat -> Nat
sumaNat n m = intToNat2((natToInt2 n)+(natToInt2 m))

--5
data BinTree a = Nill | Node (BinTree a) a (BinTree a) deriving Show

--6
sizeTree :: BinTree a -> Int
sizeTree Nill = 0
sizeTree (Node izq n der) = 1+sizeTree izq+sizeTree der

--7
heightTree :: BinTree a -> Int
heightTree Nill = 0
heightTree (Node izq n der) = 1+max (heightTree izq) (heightTree der)

-------------------------Práctico 7-------------------------
--1
-- (P -> Q) v (Q -> P) ≡ True
--      P -> Q ≡ -P v Q
-- -P v Q v -Q v P
--      CONMUTATIVA v
-- -P v P v -Q v Q
--      TERCERO EXCLUIDO
-- TRUE v TRUE
--      ABSORCIÓN
-- TRUE

-- P -> Q ≡ -P v Q
--      DEFINICIÓN ->
-- P v Q ≡ Q
--      NEUTRO PARA v
-- P v Q ≡ Q v False
--      CONMUTATIVA DE v
-- Q v P ≡ Q v False
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- Q v (P ≡ False)
--      CONTRAPOSICIÓN DE P
-- Q v -P
--      CONMUTATIVA DE v
-- -P v Q

-- P v (P ∧ Q) ≡ P
--      DISTRIBUTIVA v
-- (P v P) ∧ (P v Q) ≡ P
--      IDEMPOTENCIA
-- P ∧ (P v Q) ≡ P
--      REGLA DORADA
-- P v Q ≡ (P v Q) v P
--      ASOCIATIVA
-- P v Q ≡ (P v P) v Q
--      IDEMPOTENCIA
-- P v Q ≡ P v Q

--2
--2.1
-- A ≡ A ∧ -B
--      REGLA DORADA
-- -B ≡ -B v A
--      CONMUTATIVA v Y SIMETRIA
-- A v -B ≡ B
--      DEFINICIÓN ->
-- A -> -B
-- Quiere decir que si A es caballero entonces B es mentiroso.
-- Se puede seguir disminuyendo la expresión.
--      P -> Q ≡ -P v Q
-- -A v -B
--      DE MORGAN v
-- -(A ∧ B)

--2.2
-- A ≡ -A ∧ B
--      REGLA DORADA
-- A ≡ -A ≡ B ≡ B v -A
--      ASOCIATIVA ≡
-- (A ≡ -A) ≡ B ≡ B v -A
--      CONTRAPOSITIVA
-- FALSE ≡ B ≡ B v -A
--      ASOCIATIVA ≡
-- (FALSE ≡ B) ≡ B v -A
--      CONTRAPOSITIVA
-- -B ≡ B v -A
--      REGLA DORADA
-- -B ≡ B ≡ -A ≡ -A v B
--      ASOCIATIVA ≡
-- (-B ≡ B) ≡ -A ≡ -A v B
--      CONTRAPOSITIVA
-- FALSE ≡ -A ≡ -A v B
--      ASOCIATIVA Y NEUTRO v
-- FALSE ≡ (-A v FALSE ≡ (-A v B))
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- FALSE ≡ A v (FALSE ≡ B)
--      CONTRAPOSITIVA
-- FALSE ≡ A v -B
--      CONTRAPOSITIVA
-- -(A v -B)
--      DISTRIBUTIVA -
-- -A v B
-- Esto quiere decir que A es un mentiroso o B es un caballero

--2.3
-- A ≡ A ∧ B
--      SIMETRIA
-- A ∧ B ≡ A
--      REGLA DORADA
-- B ≡ B v A
--      NEUTRO v
-- B v FALSE ≡ B v A
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- B v (FALSE ≡ A)
--      CONTRAPOSITIVA
-- B v -A
-- Esto quiere decir que B es caballero o A es mentiroso

--2.4
-- A ≡ -A v -B
--      REGLA DORADA
-- A ≡ -A ∧ -B ≡ -A ≡ -B
--      SIMETRIA Y ASOCIATIVA ≡
-- (A ≡ -A) ≡ -B ≡ -A ∧ -B
--      CONTRAPOSITIVA
-- FALSE ≡ -B ≡ -A ∧ -B
--      SIMETRIA
-- FALSE ≡ -A ∧ -B ≡ -B
--      REGLA DORADA (A ∧ B ≡ B ≡ A ≡ B v A)
-- FALSE ≡ -A ≡ -B v -A
--      NEUTRO Y CONMUTATIVA v
-- FALSE ≡ -A v FALSE ≡ -A v -B
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- FALSE ≡ -A v (FALSE ≡ -B)
--      CONTRAPOSITIVA
-- FALSE ≡ -A v B
--      CONTRAPOSITIVA
-- A v -B
-- Esto quiere decir que A es caballero o B es mentiroso.

--2.5
-- A ≡ -A v B
--      REGLA DORADA
-- A ≡ B ≡ -A ≡ -A ∧ B
--      SIMETRIA Y ASOCIATIVA
-- (A ≡ -A) ≡ B ≡ -A ∧ B
--      CONTRAPOSITIVA
-- FALSE ≡ B ≡ -A ∧ B
--      REGLA DORADA (A y B ≡ B ≡ A ≡ B v A)
-- FALSE ≡ -A ≡ B v -A
--      NEUTRO Y CONMUTATIVA v
-- FALSE ≡ -A v FALSE ≡ -A v B
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- FALSE ≡ -A v (FALSE ≡ B)
--      CONTRAPOSITIVA
-- FALSE ≡ -A v -B
--      CONTRAPOSITIVA
-- A v B
-- Esto quiere decir que A o B es un caballero.

--2.6
-- A ≡ A -> S -> S
--      DEFINICIÓN ->
-- A ≡ A -> (S v S ≡ S)
--      IDEMPOTENCIA Y NEUTRO ≡
-- A ≡ A -> S
--      DEFINICIÓN ->
-- A ≡ A v S ≡ S
--      NEUTRO Y CONMUTATIVA v
-- A ≡ S v A ≡ S v FALSE
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- A ≡ S v (A ≡ FALSE)
--      CONTRAPOSITIVA
-- A ≡ S v -A
--      REGLA DORADA
-- A ≡ S ≡ -A ≡ A y S
--      SIMETRIA Y ASOCIATIVA ≡
-- (A ≡ -A) ≡ S ≡ A y S
--      CONTRAPOSITIVA
-- FALSE ≡ S ≡ A y S
--      REGLA DORADA
-- FALSE ≡ A ≡ S v A
--      NEUTRO Y CONMUTATIVA v
-- FALSE ≡ A v FALSE ≡ A v S
--      (A v B) ≡ (A v C) ≡ A v (B ≡ C)
-- FALSE ≡ A v (FALSE ≡ S)
--      CONTRAPOSITIVA
-- FALSE ≡ A v -S
--      CONTRAPOSITIVA
-- -A v S
-- Esto quiere decir que A es mentiroso o se come el sombrero.

-------------------------EJERCICIOS EXTRAS PASADOS POR SLACK-------------------------
--1.a
f :: Int -> [Int] -> Bool
f n [] = False
f 0 xs = False
f n xs = sum [1 | i <- [0..n-1], j <- take (n-1) xs, i == j, count j xs > 1] > 0
    where count x xs = length(filter (==x) xs)
    
--1.b
--

--1.c
--

--2
--Dado las definiciones:
--K.x.y = x
--inf = inf+1
--
--NORMAL
--K.3.inf
--  DEFINICIÓN K
--3
--
--APLICATIVA
--K.3.inf
--  DEFINICIÓN inf
--K.3.(inf+1)
--  DEFINICIÓN inf
--K.3.((inf+1)+1)
-- ...

--3.a
data BinTreeHoja a = Hoja | Nodo (BinTreeHoja a) a (BinTreeHoja a) deriving Show

--3.b
cantHojas :: (BinTreeHoja a) -> Int
cantHojas Hoja = 1
cantHojas (Nodo izq n Hoja) = 1+cantHojas izq
cantHojas (Nodo Hoja n der) = 1+cantHojas der
cantHojas (Nodo izq n der) = cantHojas izq+cantHojas der

--4, ANALIZAR POR QUE ANDA PERO NO ENTENDI BIEN POR QUE
darCoordDiagonalmente :: [(Int,Int)]
darCoordDiagonalmente = [(j,i-j) | i <- [0..6], j <- [0..i], i>=j]

coordSolo = [(i,j) | i <- [0..6], j <- [0..i], i == j]

matrizPares = [(i,j) | i <- [0..10], j <- [0..i], mod i 2 == 0, mod j 2 == 0]

matrizMult3 = (1,1):[(i,j) | i <- [1..10], mod i 3 == 0, j <- [1..i], mod j 3 == 0]

--5
--5.a
--square x = x*x
--
--inf = inf+1
--
--and true true = true
--and true false = false
--and false true = false
--and false false = false
--
--APLICATIVO
--and ((square 2) == 5)(inf == inf)
--  DEFINICIÓN square
--and ((2*2) == 5)(inf == inf)
--  ARITMETICA
--and (4 == 5)(inf == inf)
--  4 == 5
--and FALSE*(inf == inf)
--  DEFINICIÓN inf
--and FALSE*(inf+1 == inf)
--  DEFINICIÓN inf
--and FALSE*((inf+1)+1 == inf)
--  ...
--
--NORMAL
--and ((square 2) == 5)(inf == inf)
--  DEFINICIÓN square
--and ((2*2) == 5)(inf == inf)
--  ARITMETICA
--and (4 == 5)(inf == inf)
--  4 == 5
--and FALSE*(inf == inf)
--  DEFINICIÓN inf
--and FALSE*(inf+1 == inf)
--  DEFINICIÓN inf
--and FALSE*((inf+1)+1 == inf)
--  ...

--5.b
--square x = x*x
--
--inf = inf+1
--
--and true n = n
--and false n = false
--
--APLICATIVO
--and ((square 2) == 5)(inf == inf)
--  DEFINICIÓN square
--and ((2*2) == 5)(inf == inf)
--  ARITMETICA
--and (4 == 5)(inf == inf)
--  4 == 5
--and FALSE*(inf == inf)
--  DEFINICIÓN inf
--and FALSE*(inf+1 == inf)
--  DEFINICIÓN inf
--and FALSE*((inf+1)+1 == inf)
--  ...
--
--NORMAL
--and ((square 2) == 5)(inf == inf)
--  DEFINICIÓN square
--and ((2*2) == 5)(inf == inf)
--  ARITMETICA
--and (4 == 5)(inf == inf)
--  4 == 5
--and FALSE*(inf == inf)
--  DEFINICIÓN and
--FALSE

-------------------------PRÁCTICA DE PARCIAL 1-------------------------
--1
f1 :: BinTree Int -> Int
f1 Nill = 0
f1 (Node Nill n Nill) = n
f1 (Node izq n Nill) = n+f1 izq
f1 (Node Nill n der) = n+f1 der
f1 (Node izq n der) = n+f1 izq+f1 der

--2
data SIntExp = Cte Int | Sum SIntExp SIntExp | Mul SIntExp SIntExp deriving Show

--Sum (Cte 5) (Cte 5)
--Mul (Cte 0) (Cte 1)
--Cte 111
--Sum (Mul (Cte 2) (Cte 5)) (Cte 7)

--Sum (Cte 4) (Mul (Cte 3) (Cte 0))

--3
compact :: [Int] -> [Int]
compact [] = []
compact [x] = [x]
compact (x:xs) = if x == head xs then compact xs else x:compact xs

-- compact [4,3,0,6,2,6,8,2]
--      [compact (x:xs) -> (x == head xs) = compact xs
--                         otherwise = x:compact xs]
--      DEFINICIÓN COMPACT
-- (4:compact [3,0,6,2,6,8,2])
--      DEFINICIÓN COMPACT
-- (4:3:compact [0,6,2,6,8,2])
--      DEFINICIÓN COMPACT
-- (4:3:0:compact [6,2,6,8,2])
--      DEFINICIÓN COMPACT
-- (4:3:0:6:compact [2,6,8,2])
--      DEFINICIÓN COMPACT
-- (4:3:0:6:2:compact [6,8,2])
--      DEFINICIÓN COMPACT
-- (4:3:0:6:2:6:compact [8,2])
--      DEFINICIÓN COMPACT
-- (4:3:0:6:2:6:8:compact [2])
--      [compact [x] = [x]]
--      DEFINICIÓN COMPACT
-- (4:3:0:6:2:6:8:2)
--      

--4.1
--NORMAL
--(square inf)+(square inf)
--  DEFINICIÓN SQUARE
--(inf*inf)+(square inf)
--  DEFINICIÓN INF
--((inf+1)*inf)+(square inf)
--  DEFINICIÓN INF
-- (((inf+1)+1)*inf)(square inf)
-- ..., se va al infinito
--square 2
--APLICATIVO
--(square inf)+(square inf)
--  DEFINICIÓN SQUARE
--(inf*inf)+(square inf)
--  DEFINICIÓN INF
--(inf*(inf+1))+(square inf)
--  ..., se va al infinito

--4.2
--NORMAL
--and(inf == inf) ((square 2) == 4)
--  DEFINICIÓN INF
--and((inf+1) == inf) ((square 2) == 4)
--  DEFINICIÓN INF
--and(((inf+1)+1) == inf) ((square 2) == 4)
--  ..., se va al infinito
--
--APLICATIVO
--and(inf == inf) ((square 2) == 4)
--  DEFINICIÓN INF
--and((inf+1) == inf) ((square 2) == 4)
--  DEFINICIÓN INF
--and(((inf+1)+1) == inf) ((square 2) == 4)
--  ..., se va al infinito

-------------------------PRÁCTICA DE PARCIAL 2-------------------------
--1
-- imp :: Bool -> Bool -> Bool
-- imp True False = False
-- imp n m = True
--
--1.a
--NORMAL
-- imp (inf == inf) (inf == inf)
--      DEFINICIÓN INF
-- imp (inf+1 == inf) (inf == inf)
--      DEFINICIÓN INF
-- imp ((inf+1)+1 == inf) (inf == inf)
-- ..., se va al infinito
--
--APLICATIVO
-- imp (inf == inf) (inf == inf)
--      DEFINICIÓN INF
-- imp (inf+1 == inf) (inf == inf)
--      DEFINICIÓN INF
-- imp ((inf+1)+1 == inf) (inf == inf)
-- ..., se va al infinito
--
--1.b
--NORMAL
-- imp (inf == 5) True
--      DEFINICIÓN INF
-- imp (inf+1 == 5) True
--      DEFINICIÓN INF
-- imp ((inf+1)+1 == 5) True
--  ..., se va al infinito
--
--APLICATIVO
-- imp (inf == 5) True
--      DEFINICIÓN INF
-- imp (inf+1 == 5) True
--      DEFINICIÓN INF
-- imp ((inf+1)+1 == 5) True
--  ..., se va al infinito
--
--1.c
--NORMAL
-- imp False (inf == inf)
--      DEFINICIÓN IMP
-- True
--
--APLICATIVO
-- imp False (inf == inf)
--      DEFINICIÓN INF
-- imp False (inf+1 == inf)
--      DEFINICIÓN INF
-- imp False ((inf+1)+1 == inf)
--  ..., se va al infinito

--2
--intToNat 0 = Zero
--intToNat n = Succ (intToNat (n-1))
--
--natToInt Zero = 0
--natToInt (Succ n) = 1+natToInt(n)
--
--2.a
--sum :: Nat -> Nat -> Nat
--sum n m = intToNat((natToInt(n))+(natToInt(m)))
--
--2.b
--mult :: Nat -> Nat -> Nat
--mult n m = intToNat((natToInt(n))*(natToInt(m)))
--
--2.c
--par :: Nat -> Bool
--par n = mod (natToInt(n)) 2 == 0

--3
flatten2 :: [[a]] -> [a]
flatten2 [] = []
flatten2 [x] = x
flatten2 (x:xs) = x ++ flatten2 xs

--4
count2 :: [Int] -> Int -> Int
count2 xs n = sum [1 | i <- xs, i == n]

-------------------------PRÁCTICA PERSONAL-------------------------

reverseTree :: BinTree a -> BinTree a
reverseTree (Node Nill n Nill) = Node Nill n Nill
reverseTree (Node Nill n der) = Node (reverseTree der) n Nill
reverseTree (Node izq n Nill) = Node Nill n (reverseTree izq)
reverseTree (Node izq n der) = Node (reverseTree der) n (reverseTree izq)

tamTree :: BinTree a -> Int
tamTree Nill = 0
tamTree (Node izq n der) = 1+tamTree izq +tamTree der

alturaTree :: BinTree a -> Int
alturaTree Nill = 0
alturaTree (Node izq n der) = max (alturaTree izq+1) (alturaTree der+1)

cantNills :: BinTree a -> Int
cantNills Nill = 1
cantNills (Node Nill n der) = 1+cantNills der
cantNills (Node izq n Nill) = 1+cantNills izq
cantNills (Node izq n der) = cantNills izq + cantNills der

sumaValTree :: Num a => BinTree a -> a
sumaValTree (Node Nill n Nill) = n
sumaValTree (Node izq n Nill) = n+sumaValTree izq
sumaValTree (Node Nill n der) = n+sumaValTree der
sumaValTree (Node izq n der) = n+sumaValTree izq+sumaValTree der

--foldl: toma una función, un acumulador (neutro) y una lista. 
--       Evalua de izquierda a derecha.
--       foldl :: (b -> a -> b) -> b -> [a] -> b
--       EJ: foldl (+) 0 [1,2,3,4]
--           (((0+1)+2)+3)+4
--
--foldr: toma una función, un acumulador (neutro) y una lista.
--       Evalua de derecha a izquierda.
--       foldr :: (a -> b -> b) -> b -> [a] -> b
--       EJ: foldr (+) 0 [1,2,3,4]
--           1+(2+(3+(4+0)))

--Diferencias entre foldl y foldr
-- ●DIRECCIÓN: foldl evalua de izquierda a derecha, foldr de derecha a izquierda.
--      foldl suma el acumulador (neutro) al primer elemento de la lista y seguira
--      con el segundo elemento de la lista, mientras que foldr sumara el acumulador
--      (neutro) con el último elemento de la lista y con el resultado de esto
--      seguira con el penúltimo elemento.
-- ●TIPO DE PLEGADO: foldl tiene plegado estricto, esto quiere decir que se evaluan
--      todos los elementos de la lista antes de comenzar a plegarla, lo cual
--      impactara mucho en el rendimiento al utilizar listas grandes.
--      Mientras que foldr es de plegado perezoso, lo que quiere decir que solo se
--      evalua el elemento actual de la lista cuando es necesario para la evaluación
--      de la función acumuladora.
-- ●LISTAS INFINITAS: foldl no podria realizar una lista infinita debido a que tendria
--      que primero evaluar todos los elementos de la misma, a la que nunca llegaria
--      a terminar de evaluar.
--      Mientras que con foldr, solo es necesario que evalua su primer elemento y de
--      ahi llegue al primer elemento de la lista.

--Ventajas/Desventajas de foldl y foldr
-- ●VENTAJAS FOLDR
--      -Es más adecuado para trabajar con listas infinitas.
--      -Es más eficientes cuando se puede aprovechar el plegado de derecha a
--       izquierda, cómo cuando creamos una lista inversa.
-- ●DESVENTAJAS FOLDR
--      -NO se puede utilizar para estructuras de datos que no sean listas.
--      -No es adecuado para funciones que requieren un orden de evaluación de
--       izquierda a derecha.
--
-- ●VENTAJAS FOLDL
--      -Se puede usar en estructuras de datos que no sean listas, cómo con
--       árboles o grafos.
--      -Puede ser más eficientes cuando se requiere una evaluación de izquierda a
--       derecha.
-- ●DESVENTAJAS FOLDL
--      -No se puede utilizar para trabajar listas infinitas.
--      -La evaluación de izquierda a derecha puede ser menos intuitiva en algunos
--       casos.

--DEFINICIONES DE ALGUNAS FUNCIONES DE ALTO ORDEN:
--  ●map :: (a -> b) -> [a] -> [b]
--      (a -> b) = dado un a, devuelve b que es un a modificado
--      map (*2) [1,2,3] = [2,4,6]
--
--  ●filter :: (a -> Bool) -> [a] -> [a]
--      (a -> Bool) = dado un a, devuelve un Booleano si cumplea una condición
--      filter (==2) [1,2,3,2] = [2,2]
--
--  ●zip :: [a] -> [b] -> [(a,b)]
--      zip [1,2,3] [4,5,6] = [(1,4), (2,5), (3,6)]
--

matriz5 = [(i,j) | i <- [0..5], j <- [0..10]]
diagMatriz = [(i,i) | i <- [0..5]]
diagMatriz2 = [(i,j) | i <- [0..5], j <- [0..10], i == j]
abajoDiag = [(i,j) | i <- [0..5], j <- [0..10], i > j]
arribaDiag = [(i, j) | i <- [0..5], j <- [0..10], i < j]
todosDivs = [(i,j) | i <- [0..5], j <- [0..10], j /= 0 && i /= 0 && mod i j == 0]
pares = [(i,j) | i <- [0..5], even i, j <- [0..10], even j]

--FUNCIONES LAMBDA
-- Son funciones inline, es decir, que pueden ser usadas cómo argumento o expresión
-- en otra función sin la necesidad de definirlas.
-- Sintaxis: (\argumentos -> cuerpo de la función)
--
-- EJ: suma x y = x+y
--     suma = \x y -> x+y