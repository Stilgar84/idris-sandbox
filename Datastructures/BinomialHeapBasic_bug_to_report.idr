
module BinomialHeapBasic

%default total

--------------------------------------------------------------------------------
-- Types declaration
--
mutual 
  data BinomialLeafs : a -> (k:Nat) -> Type where
    emptyLeaf  : BinomialLeafs a Z
    consLeaf : BinomialTree a k -> BinomialLeafs a k -> BinomialLeafs a (S k)
 
  data BinomialTree : a -> (k:Nat) -> Type where
    mkBinTree : a -> (BinomialLeafs a k) -> BinomialTree a k

data BinomialHeap a = mkBinHeap (List (k ** BinomialTree a k))
--------------------------------------------------------------------------------

-- obviously need comparison to know to merge right or left
mergeTree : BinomialTree a k -> BinomialTree a k -> BinomialTree a (S k)
mergeTree x (mkBinTree ry ly) = mkBinTree ry (consLeaf x ly)

merge : BinomialHeap a -> BinomialHeap a -> BinomialHeap a
merge (mkBinHeap al) (mkBinHeap bl) = mkBinHeap $ mergeList al bl
  where
    mergeList : (List (k ** BinomialTree a k)) -> (List (k ** BinomialTree a k)) -> List (k ** BinomialTree a k)
    mergeList [] bL = bL
    mergeList aL [] = aL
    -- The bug is here, idris seems to go to this case even when the value of k are different
    -- this create invalid datastructure
    mergeList ((k ** ax)::at) ((k ** bx)::bt) = (_**mergeTree ax bx) :: (mergeList at bt)


--------------------------------------------------------------------------------
-- Insertion: just merge with a heap containing one element
insert : a -> BinomialHeap a -> BinomialHeap a
insert x heap = merge (mkBinHeap xlist) heap
	where
		xtree : BinomialTree a 0
		xtree = mkBinTree x emptyLeaf
		xlist = (_ ** xtree)::List.Nil
--------------------------------------------------------------------------------

testT : BinomialTree Char 2
testT = mkBinTree 'c' (
  consLeaf 
    (mkBinTree 'b' (consLeaf (mkBinTree 'a' emptyLeaf) emptyLeaf))
    (consLeaf (mkBinTree 'a' emptyLeaf) emptyLeaf))

testM : BinomialHeap Char
testM = insert 'a' $ insert 'b' $ insert 'c' (mkBinHeap [])

testE : BinomialTree Char 2
--testE = mkBinTree 'c' (consLeaf (mkBinTree 'a' emptyLeaf) (consLeaf (mkBinTree 'b' emptyLeaf) emptyLeaf))

