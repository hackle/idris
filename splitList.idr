data SplitList : List a -> Type where
  SplitNil : SplitList []
  SplitOne : SplitList [x]
  SplitPair : (left: List a) -> (right: List a) -> SplitList (left ++ right)

total
splitListHelper : List a -> (input: List a) -> SplitList input
splitListHelper _ [] = SplitNil
splitListHelper _ (x :: []) = SplitOne
splitListHelper (_::_::counter) (item :: items) = case splitListHelper counter items of
                                                 SplitNil => SplitOne
                                                 SplitOne {x} => SplitPair [item] [x]
                                                 (SplitPair left right) => SplitPair (item::left) right
splitListHelper _ items = SplitPair [] items

splitList : (input: List a) -> SplitList input
splitList input =splitListHelper input input

splitList1 : (input: List a) -> SplitList input
splitList1 [] = SplitNil
splitList1 (x :: []) = SplitOne
splitList1 (x :: (y :: xs)) = case splitList1 xs of
                                    SplitNil => SplitPair [x] [y]
                                    SplitOne {x=x1} => SplitPair [x] [y, x1]
                                    (SplitPair left right) => ?splitList1_rhs_4

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (left ++ right) | (SplitPair left right) = merge (mergeSort left) (mergeSort right)
