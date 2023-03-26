--1- (2^20) == (2^29)/(2^9)

--2- head(tail("hola mundo"))

--3- head(reverse("hola mundo"))

--4- :t

--5- mod (head(reverse([1,2,3]))) 2 == 0

--6- mod (sum [1,2,0]) 3 == 0

--7- mod (sum [1,2,0]) 3 == 0 || mod (sum [1,2,0]) 6 == 0

--8- En archivo .hs
list :: Int -> [Int]
list 0 = []
list n = list (div n 10)++[mod n 10]

--9-["o","l","o"] == reverse(["o","l","a"])

--10-(head.(drop 3)) "0123456" = '3'
--Es de tipo Char
--Se podria implementar con muchos tails 
    --head(tail(tail(tail("0123456"))))
--

--11-

--12-

--Ejemplos
doubleMe x = x+x
doubleUs x y = doubleMe x + doubleMe y
doubleSmallNumber x = if x > 100
                        then x
                        else x*2