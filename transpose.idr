import Data.Vect

createEmpties : Vect m (Vect 0 a)
createEmpties {m = Z} = []
createEmpties {m = (S k)} = [] :: createEmpties

addHead : (x : Vect m a) -> (rest : Vect m (Vect len a)) -> Vect m (Vect (S len) a)
addHead x rest = Vect.zipWith (::) x rest

trans: Vect n (Vect m a) -> Vect m (Vect n a)
trans [] = createEmpties
trans (x :: xs) = let rest = trans xs in (addHead x rest)

addHeads : Num a => (x : Vect n a) -> (y : Vect n a) -> a
addHeads x y = foldl (+) 0 $ zipWith (*) x y

getHeads : Num a => (x : Vect n a) -> (ys : Vect p (Vect n a)) -> Vect p a
getHeads x [] = []
getHeads x (y :: xs) = let rest = getHeads x xs in addHeads x y :: rest

multM_rhs : Num a => (xs : Vect m (Vect n a)) -> (ys : Vect p (Vect n a)) -> Vect m (Vect p a)
multM_rhs [] ys = []
multM_rhs (x :: xs) ys = let xss = multM_rhs xs ys in getHeads x ys :: xss

multM : Num a => Vect m (Vect n a) -> Vect n (Vect p a) -> Vect m (Vect p a)
multM xs ys = let yss = trans ys in (multM_rhs xs yss)
