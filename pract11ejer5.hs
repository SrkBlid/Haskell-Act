split2 :: [a] -> [([a], [a])]
split2 [] = []
split2 xs = [splitAt n xs | n <- [0..length xs]]

--prim :: [(a,b)] -> (a,b)
--prim [] = ( , )
--prim [x] = x
--prim (x:xs) = x

fstL :: (a, b) -> a
fstL (a, b) = a

sndL :: (a, b) -> b
sndL (a, b) = b

--split3 :: [a] -> [([a], [a], [a])]
--split3 [] = []
--split3 xs = [(take n xs, fstL (prim (split2 (drop n xs))), sndL (prim (split2 (drop n xs)))) | n <- [0..length xs]]

--split2 [1,2]
--  [1,2] []
--  [] [1,2]
--  [1] [2]

--split3 [1,2]
--  [1,2] [] []
--  [] [1,2] []
--  [] [] [1,2]
--  [1] [2] []
--  [1] [] [2]
--  [] [1] [2]

--La especificaciòn del ejercicio 1(e)
-- <∏i : 0 <= i <= #xs ∧ esPrimo(i) : xs.i>
-- ==

eUno :: [Int] -> Int
eUno xs = product [xs !! i | i <- [0..length (xs)-1], esPrimo(xs!!i)]

eUno2 :: [Int] -> Int
eUno2 xs = product [x | x <- xs, esPrimo(x)]

esPrimo :: Int -> Bool
esPrimo n = divs n 1 <= 2 
    where divs n i
            | n == i = 0
            | mod n i == 0 = 1+divs n (i+1)
            | otherwise = divs n (i+1)
            

