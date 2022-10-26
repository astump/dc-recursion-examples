module Rle where


--------------------------------------------------------------------------------
--
mapThrough :: (a -> [a] -> (b, [a])) -> [a] -> [b]
mapThrough f [] = []
mapThrough f (a : as) = b : mapThrough f as'
  where (b, as') = f a as

rle :: Eq a => [a] -> [(Int, a)]
rle = mapThrough compressSpan
  where compressSpan a as =
          let (p, s) = span (== a) as in
            ((1 + length p, a), s)
  
