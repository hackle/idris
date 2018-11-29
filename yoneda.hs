fw :: Functor f => ((a -> b) -> f b) -> f a
fw g = g id
