#lang hackett

(require hackett/private/test)

;; The purpose of `countA` is to be a recursive function that makes enough
;;  recursive calls to "run forever" if string patterns aren't forced
(defn countA : {String -> Integer}
  [[""] 0]
  [["A"] 1]
  [[other] (+ (countA (head! (string-split "B" other)))
              (countA (head! (tail! (string-split "B" other)))))])

(test {(countA "ABA") ==! 2})
