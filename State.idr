data State s a = St (s -> (s, a))

runState : State s a -> s -> a
runState (St f) s = snd $ f s

Functor (State s) where
  map f (St g) = St $ \s => f <$> g s

Applicative (State s) where
  pure a = St $ \s => (s, a)

  (St f) <*> (St g) = St $ \s => let (s1, f1) = f s in f1 <$> g s1

Monad (State s) where
  (St g) >>= f = St $ \s => let (s1, a) = g s;
                                (St h) = f a in h s1

getS : State s s
getS = St $ \s => (s, s)

putS : s -> State s ()
putS s = St $ \_ => (s, ())

test1 : State Int String
test1 = do
  cnt <- getS
  putS (cnt + 1)
  cnt' <- getS
  if cnt' < 5
    then test1
    else pure $ "stops at " ++ show cnt'
