module WordsBy where

import Prelude hiding (span, break)

--------------------------------------------------------------------------------
-- Section 3, Figure 1
--------------------------------------------------------------------------------

wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p [] = []
wordsBy p (hd:tl) =
  if p hd
     then wordsBy p tl
     else let (w, z) = break p tl in
              (hd : w) : wordsBy p z


span :: (a -> Bool) -> [a] -> ([a], [a])
span _ [] = ([], [])
span p xs@(x:xs') =
  if p x
  then let (r, s) = span p xs' in
       (x : r, s)
  else ([], xs)

break p = span (not . p)
