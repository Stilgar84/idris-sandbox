
-- Basic seens we will not try to prove much, only the binomial tree structure
module BinomialHeapBasic

%default total

-- TODO we could want to provide the compare functor as parameter to allow
-- creating min and max heap and other stuff?
-- => not needed, see https://github.com/idris-lang/Idris-dev/blob/master/samples/named_instance.lidr

--------------------------------------------------------------------------------
-- Types declaration
--
mutual 
  data BinomialLeafs : a -> (k:Nat) -> Type where
    Nil  : BinomialLeafs a Z
    (::) : BinomialTree a k -> BinomialLeafs a k -> BinomialLeafs a (S k)
 
  data BinomialTree : a -> (k:Nat) -> Type where
    mkBinTree : a -> (BinomialLeafs a k) -> BinomialTree a k

data BinomialHeap a = mkBinHeap (List (k ** BinomialTree a k))
--------------------------------------------------------------------------------

-- obviously need comparison to know to merge right or left
mergeTree : BinomialTree a k -> BinomialTree a k -> BinomialTree a (S k)
mergeTree x (mkBinTree ry ly) = mkBinTree ry (x :: ly)

-- need to ensure ordering and unicity of k
-- we may want a sized version of the heap?

merge : BinomialHeap a -> BinomialHeap a -> BinomialHeap a
merge (mkBinHeap al) (mkBinHeap bl) = mkBinHeap $ mergeList al bl
  where
    mergeList : (List (k ** BinomialTree a k)) -> (List (k ** BinomialTree a k)) -> List (k ** BinomialTree a k)
    mergeList [] bL = bL
    mergeList aL [] = aL
    mergeList ((ak ** ax)::at) ((bk ** bx)::bt) with (cmp ak bk)
      mergeList ((k ** ax)::at) ((k ** bx)::bt) | cmpEQ = mergeList (mergeList [(_**mergeTree ax bx)] at) bt
      mergeList ((_ ** ax)::at) ((_ ** bx)::bt) | cmpLT _ = (_** ax) :: (mergeList at bl)
      mergeList ((_ ** ax)::at) ((_ ** bx)::bt) | cmpGT _ = (_** bx) :: (mergeList al bt)
 


--------------------------------------------------------------------------------
-- Insertion: just merge with a heap containing one element
insert : a -> BinomialHeap a -> BinomialHeap a
insert x heap = merge (mkBinHeap xlist) heap
	where
		xtree : BinomialTree a 0
		xtree = mkBinTree x Nil
		xlist = (_ ** xtree)::List.Nil
--------------------------------------------------------------------------------

--takeMin : BinomialHeap a -> (a, BinomialHeap a)

-- todo: add some basic unit tests
-- then start adding static constraints

testT : BinomialTree Char 2
testT = mkBinTree 'c' ((mkBinTree 'b' ((mkBinTree 'a' Nil) :: Nil))::((mkBinTree 'a' Nil) :: Nil))

testM : BinomialHeap Char
testM = insert 'e' $ insert 'd' $ insert 'a' $ insert 'b' $ insert 'c' (mkBinHeap [])
--insert 'e' $ insert 'd' $ 

--Ord a =>

--data BinomialTree : (a:Type) -> (k:Nat) -> Type where
--	mkSingle : a -> BinomialTree a Z
--	merge : BinomialTree a k -> BinomialTree a k -> BinomialTree a (S k)


