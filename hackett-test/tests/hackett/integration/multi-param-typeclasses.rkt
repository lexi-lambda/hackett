#lang hackett

(require hackett/private/test)

(class (Coerce a b)
  [coerce : {a -> b}])

(instance (Coerce Integer String)
  [coerce show])

(instance (Coerce Integer Double)
  [coerce integer->double])

(test {(: (coerce 5) String) ==! "5"})
(test {{{5.0 d- (coerce 5)} d< 0.1} ==! true})
