import Data.Vect

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word: String) ->
                (missing: Vect letters Char) ->
                WordState guesses_remaining letters

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

noNilInput : ValidInput [] -> Void
noNilInput (Letter _) impossible

noExtra : ValidInput (x :: (y :: xs)) -> Void
noExtra (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No noNilInput
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No noExtra

isValidString : (str : String) -> Dec (ValidInput (unpack str))
isValidString str = isValidInput $ unpack str

readGuess : IO (x ** ValidInput x)
readGuess = do {
    str <- getLine
    case isValidString str of
      (Yes prf) => pure (_ ** prf)
      (No contra) => do putStrLn "Incorrect guess, try again"
                        readGuess
  }

processGuess : (letter : Char) ->
                WordState (S guesses) (S letters) ->
                Either (WordState guesses (S letters)) (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) =
  case isElem letter missing of
      (Yes prf) => Right (MkWordState word (dropElem missing prf))
      (No contra) => Left (MkWordState word missing)

play : WordState (S guesses) (S letters) -> IO Finished
play game {guesses} {letters} = do
                                  (_ ** Letter c) <- readGuess
                                  case processGuess c game of
                                      (Left l) => case guesses of
                                        Z => pure (Lost l)
                                        (S k) => do
                                          putStrLn $ "not right, " ++ (show guesses) ++ "remaining"
                                          play l
                                      (Right r) => case letters of
                                        Z => pure (Won r)
                                        (S k) => do
                                          putStrLn $ "good, keep going!"
                                          play r

main : IO ()
main = do
    putStrLn "game has started!"
    result <- play (MkWordState "blue" ['b', 'l', 'u', 'e'] {guesses_remaining=3})
    case result of
      (Lost game) => putStrLn "You have lost!"
      (Won game) => putStrLn "You have won"
