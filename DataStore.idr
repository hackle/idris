module Main

import Data.Vect

data DataStore : Type where
  MkData : (size: Nat) -> (items: Vect size String) -> DataStore

size : DataStore -> Nat
size (MkData size items) = size

items : (ds: DataStore) -> Vect (size ds) String
items (MkData size items) = items

appendV : String -> Vect m String -> Vect (S m) String
appendV x [] = [x]
appendV x (y :: xs) = y :: appendV x xs

addToStore : String -> DataStore -> DataStore
addToStore x (MkData size items) = MkData (S size) (appendV x items)

data Command = Add String
              | Get Integer
              | Quit

parse : String -> Maybe Command
parse str = case span (/= ' ') str of
                 ("add", content) => Just $ Add content
                 ("get", index) => (case all isDigit (unpack $ ltrim index) of
                                         True => Just (Get (cast index))
                                         False => Nothing)
                 ("quit", _) => Just Quit
                 _ => Nothing

process_input : DataStore -> String -> Maybe (String, DataStore)
process_input ds command = case parse command of
                                Nothing => Just ("try again", ds)
                                (Just (Add x)) => Just (">", addToStore x ds)
                                (Just (Get idx)) => (case integerToFin idx (size ds) of
                                                          Nothing => Just ("not found", ds)
                                                          (Just findex) => let item = Vect.index findex (items ds) in Just (show item, ds))
                                (Just Quit) => Nothing

data VectU : Type -> Type where
  MkVectU : Vect len a -> VectU a

sizeVU : VectU a -> Nat
sizeVU (MkVectU xs) = length xs

addUV : a -> VectU a -> VectU a
addUV x (MkVectU xs) = MkVectU (x::xs)

filterVU : (a -> Bool) -> Vect m a -> VectU a
filterVU f [] = MkVectU []
filterVU f (x :: xs) = let xs1 = filterVU f xs in (case f x of
                                                        False => xs1
                                                        True => addUV x xs1)

filter1 : (a -> Bool) -> Vect m a -> (n**Vect n a)
filter1 f xs = case filterVU f xs of
                    (MkVectU xs) => (_**xs)

main : IO ()
main = replWith (MkData _ []) ">" process_input
