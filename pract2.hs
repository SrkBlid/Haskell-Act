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