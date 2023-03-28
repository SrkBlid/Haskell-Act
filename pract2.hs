--1- Leer capitulos 1 y 2 del libro

--2- 
--head, retorna el primer elemento de una lista
hd2 :: [a] -> a
hd2 (x:xs) = x

--tail, retorna toda la lista menos el primer elemento
tl2 :: [a] -> [a]
tl2 (x:xs) = xs

--last, retorna el último elemento de la lista
last2 :: [a] -> a
last2 [x] = x 
last2 (x:xs) = last2 xs

--init, retorna toda la lista menos el último elemento
init2 :: [a] -> [a]
init2 [x] = []
init2 (x:xs) = x : init2 xs

--3
maxTres :: Int -> Int -> Int -> Int
maxTres x y z
        | (x >= y) && (x >= z) = x
        | (y >= x) && (y >= z) = y
        | (z >= x) && (z >= y) = z

--4
conca :: [a] -> [a] -> [a]
conca [] [] = []
conca xs [] = xs
conca [] ys = ys
conca xs (y:ys) = y : conca xs ys

tomar :: Int -> [a] -> [a]
tomar 0 xs = []
tomar n [] = []
tomar n (x:xs) = x : tomar (n-1) xs

tirar :: Int -> [a] -> [a]
tirar 0 xs = xs
tirar n [] = []
tirar n (x:xs) = tirar (n-1) xs

concaF :: [a] -> [a] -> [a]
concaF xs [] = xs
concaF [] ys = ys
concaF (x:xs) ys = x : concaF xs ys

longL :: [a] -> Int
longL [] = 0
longL (x:xs) = 1+longL xs

--5
abs2 :: Int -> Int
abs2 x
    | x < 0 = x*(-1)
    | x >= 0 = x

--6
edad :: (Int,Int,Int) -> (Int,Int,Int) -> Int
edad (a,b,c) (d,e,f)
        | c >= f = c-f
        | c < f = f-c

--7
xor :: Bool -> Bool -> Bool
xor x y
    | x && not y = True
    | not x && y = True
    | otherwise = False

xor2 :: Bool -> Bool -> Bool
xor2 x y
        | (x && not y) || (not x && y) = True
        | otherwise = False

--8
primN :: Int -> Bool
primN n
        | n <= 1 = False
        | length [x | x <- [1..n], mod n x == 0] == 2 = True
        | otherwise = False

--9
listPrimN :: Int -> [Int]
listPrimN n
        | n <= 1 = []
        | otherwise = [x | x <- [1..n], primN(x)]

--10
reverse2 :: [a] -> [a]
reverse2 [] = []
reverse2 (x:xs) = reverse2 xs ++ [x]

--11
igualL :: Eq a => [a] -> [a] -> Bool
igualL [] [] = True
igualL (x:xs) (y:ys) = 
        if (longL(x:xs) == longL(y:ys) && x == y) then
                igualL xs ys
        else
                False

--12
palinL :: Eq a => [a] -> Bool
palinL [] = True
palinL (n:ns) = False

--13
raicesR :: Int -> Int -> Int -> Int
raicesR a b c = 
        if b*b-4*a*c == 0 then
                1
        else
                2