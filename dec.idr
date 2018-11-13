-- an offshoot of hangman
-- what if I want to decide if a game is finished?
-- this is the outcome - but it's not needed for the game, we can simply construct
-- values for finished as we know guesses_remaining and letters 

import Data.Vect

data WordState : (guesses_remaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word: String) ->
                (missing: Vect letters Char) ->
                WordState guesses_remaining letters

data Finished : (ws: WordState guesses letters) -> Type where
  Lost : {xs: WordState { guesses_remaining = 0 } { letters = S l } } -> Finished xs
  Won : {xs: WordState { guesses_remaining = S g } { letters = 0 }} -> Finished xs

bothNil : (ws: WordState 0 0) -> Finished ws -> Void
bothNil _ Lost impossible
bothNil _ Won impossible

bothSucc : (ws: WordState (S k) (S j)) -> Finished ws -> Void
bothSucc _ Lost impossible
bothSucc _ Won impossible

isFinished : (ws: WordState guesses letters) -> Dec (Finished ws)
isFinished ws {guesses = Z} {letters = Z} = No (bothNil ws)
isFinished ws {guesses = Z} {letters = (S k)} = Yes $ Lost { xs = ws }
isFinished ws {guesses = (S k)} {letters = Z} = Yes $ Won { xs = ws }
isFinished ws {guesses = (S k)} {letters = (S j)} = No (bothSucc ws)
