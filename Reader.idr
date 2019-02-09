data Reader r a = R (r -> a)

runReader : Reader r a -> r -> a
runReader (R f) r = f r

Functor (Reader r) where
  map f (R g) = R (f . g)

Applicative (Reader r) where
  pure a = R $ const a

  (R f) <*> (R g) = R $ \r => f r (g r)

Monad (Reader r) where
  (R g) >>= f = R $ \r => runReader (f (g r)) r

testReader : Reader Int String
testReader = do
  n1 <- R (\n => show $ n + 1)
  pure n1
